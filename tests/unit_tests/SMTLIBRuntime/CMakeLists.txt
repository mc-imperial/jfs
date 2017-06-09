#===------------------------------------------------------------------------===#
#
#                         JFS - The JIT Fuzzing Solver
#
# Copyright 2017 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#

# Header only library
add_library(JFSSMTLIBRuntime INTERFACE)

target_include_directories(JFSSMTLIBRuntime
  INTERFACE "${CMAKE_SOURCE_DIR}/runtime"
)

# Header should use C++11
target_compile_options(JFSSMTLIBRuntime
  INTERFACE "${JFS_USE_CXX_FLAG}"
)

add_subdirectory(BitVector)
