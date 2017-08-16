#!/bin/bash
# This script builds JFS
set -x
set -e
set -o pipefail
: ${JFS_SRC_DIR?"JFS_SRC_DIR must be specified"}
: ${JFS_BUILD_DIR?"JFS_BUILD_DIR must be specified"}
: ${JFS_BUILD_TYPE?"JFS_BUILD_TYPE must be specified"}
: ${LLVM_BUILD_DIR?"LLVM_BUILD_DIR must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}

# Set values if not already set externally
JFS_CMAKE_GENERATOR="${JFS_CMAKE_GENERATOR:-Ninja}"
JFS_ENABLE_ASSERTIONS="${JFS_ENABLE_ASSERTIONS:-ON}"

# Setup source dir
# TODO: Support fetching from source repo

# Setup build dir
mkdir -p "${JFS_BUILD_DIR}"
cd "${JFS_BUILD_DIR}"

# Configure
cmake \
  -G "${JFS_CMAKE_GENERATOR}" \
  -DCMAKE_BUILD_TYPE=${JFS_BUILD_TYPE} \
  -DLLVM_DIR=${LLVM_BUILD_DIR}/lib/cmake/llvm \
  -DZ3_DIR=${Z3_BUILD_DIR} \
  -DENABLE_JFS_ASSERTS=${JFS_ENABLE_ASSERTIONS} \
  "${JFS_SRC_DIR}"

# Build
if [ "${JFS_CMAKE_GENERATOR}" = "Ninja" ]; then
  ninja
else
  make -j$(nproc)
fi
