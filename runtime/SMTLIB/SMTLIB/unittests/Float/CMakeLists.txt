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
add_jfs_unit_test(Float
  Native/IsNegative.cpp
  Native/IsPositive.cpp
  Native/IsNaN.cpp
  Native/IsNormal.cpp
  Native/IsSubnormal.cpp
  Native/IsZero.cpp
  Native/MakeFromIEEEBitVector.cpp
  Native/MakeFromBuffer.cpp
  Native/MakeFromTriple.cpp
  Native/SMTLIBEquals.cpp
  Native/SpecialConstants.cpp
)

target_link_libraries(Float${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
target_link_libraries(Float${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntimeTestUtil)
