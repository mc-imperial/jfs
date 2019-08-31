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

#ifndef PRF_LOG_H
#define PRF_LOG_H

#include <iostream>

namespace prf {

template<typename... Ts>
void Print(Ts... args) {
  int dummy[] = {0, (std::cout << args, 0)...};
  std::cout << std::endl;
}

template<typename... Ts>
void Debug(Ts... args) {
  int dummy[] = {0, (std::cerr << args, 0)...};
  std::cerr << std::endl;
}

} // prf

#endif // PRF_LOG_H