#!/bin/bash

# This script builds Z3
set -x
set -e
set -o pipefail
: ${Z3_SRC_DIR?"Z3_SRC_DIR must be specified"}
: ${Z3_BUILD_DIR?"Z3_BUILD_DIR must be specified"}
: ${Z3_BUILD_TYPE?"Z3_BUILD_TYPE must be specified"}

# Set values if not already set externally
Z3_GIT_REVISION="${Z3_GIT_REVISION:-b0aaa4c6d7a739eb5e8e56a73e0486df46483222}"
Z3_GIT_URL="${Z3_GIT_URL:-https://github.com/Z3Prover/z3.git}"
Z3_CMAKE_GENERATOR="${Z3_CMAKE_GENERATOR:-Ninja}"

ADDITIONAL_Z3_OPTS=()

# Static or dynamic libz3
if [ "X${Z3_STATIC_BUILD}" = "X1" ]; then
  ADDITIONAL_Z3_OPTS+=('-DBUILD_LIBZ3_SHARED=OFF')
else
  ADDITIONAL_Z3_OPTS+=('-DBUILD_LIBZ3_SHARED=ON')
fi

# Setup source tree
mkdir -p "${Z3_SRC_DIR}"
git clone "${Z3_GIT_URL}" "${Z3_SRC_DIR}"
cd "${Z3_SRC_DIR}"
git checkout "${Z3_GIT_REVISION}"

# Make build tree
mkdir -p "${Z3_BUILD_DIR}"
cd "${Z3_BUILD_DIR}"

# Configure
cmake \
  -G "${Z3_CMAKE_GENERATOR}" \
  -DCMAKE_BUILD_TYPE=${Z3_BUILD_TYPE} \
  -DUSE_OPENMP=ON"${Z3_SRC_DIR}" \
  -DUSE_LIB_GMP=FALSE \
  "${ADDITIONAL_Z3_OPTS[@]}" \
  "${Z3_SRC_DIR}"

# Build
if [ "${Z3_CMAKE_GENERATOR}" = "Ninja" ]; then
  ninja
else
  make -j$(nproc)
fi
