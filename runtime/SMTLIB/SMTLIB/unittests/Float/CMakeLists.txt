#===------------------------------------------------------------------------===#
#
#                                      JFS
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
add_jfs_unit_test(Float
  Native/Add.cpp
  Native/Abs.cpp
  Native/ConvertToFloatFromFloat.cpp
  Native/ConvertToFloatFromUnsignedBV.cpp
  Native/ConvertToFloatFromSignedBV.cpp
  Native/ConvertToUnsignedBVFromFloat.cpp
  Native/ConvertToSignedBVFromFloat.cpp
  Native/Div.cpp
  Native/FMA.cpp
  Native/GreaterThan.cpp
  Native/GreaterThanOrEqual.cpp
  Native/IEEEEquals.cpp
  Native/IsInfinite.cpp
  Native/IsNegative.cpp
  Native/IsPositive.cpp
  Native/IsNaN.cpp
  Native/IsNormal.cpp
  Native/IsSubnormal.cpp
  Native/IsZero.cpp
  Native/LessThan.cpp
  Native/LessThanOrEqual.cpp
  Native/MakeFromIEEEBitVector.cpp
  Native/MakeFromBuffer.cpp
  Native/MakeFromTriple.cpp
  Native/Max.cpp
  Native/Min.cpp
  Native/Mul.cpp
  Native/Neg.cpp
  Native/Rem.cpp
  Native/RoundToIntegral.cpp
  Native/SMTLIBEquals.cpp
  Native/Sub.cpp
  Native/SpecialConstants.cpp
  Native/Sqrt.cpp
)

target_link_libraries(Float${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
target_link_libraries(Float${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntimeTestUtil)
