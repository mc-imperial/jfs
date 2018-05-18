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

#include "Types.h"

namespace prf {

struct Options {
#define PRF_OPTION(_, type, name, value)                                       \
  type name = value;
#include "Options.def"
#undef PRF_OPTION
};

int Driver(int& argc, char**& argv);

void PrintFinalStats();

Options BuildOptions(int& argc, char**& argv);

void AbortHandler(int sig);
void TimeoutHandler(int sig);

} // prf

#endif // PRF_DRIVER_H
