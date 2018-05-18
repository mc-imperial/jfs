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

#ifndef PRF_DRIVER_H
#define PRF_DRIVER_H

namespace prf {

struct Options;

int Driver(int& argc, char**& argv);
Options BuildOptions(int& argc, char**& argv);

} // prf

#endif // PRF_DRIVER_H
