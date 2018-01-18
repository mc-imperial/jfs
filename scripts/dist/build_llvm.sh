#!/bin/bash

# This script builds LLVM
set -x
set -e
set -o pipefail
: ${LLVM_SRC_DIR?"LLVM_SRC_DIR must be specified"}
: ${LLVM_BUILD_DIR?"LLVM_BUILD_DIR must be specified"}
: ${LLVM_BUILD_TYPE?"LLVM_BUILD_TYPE must be specified"}

# Set values if not already set externally
LLVM_CMAKE_GENERATOR="${LLVM_CMAKE_GENERATOR:-Ninja}"
LLVM_BRANCH=release_60
LLVM_GIT_URL="${LLVM_GIT_URL:-http://llvm.org/git/llvm.git}"
CLANG_GIT_URL="${CLANG_GIT_URL:-http://llvm.org/git/clang.git}"
COMPILER_RT_GIT_URL="${COMPILER_RT_GIT_URL:-http://llvm.org/git/compiler-rt.git}"
LIBCXX_GIT_URL="${LIBCXX_GIT_URL:-http://git.llvm.org/git/libcxx.git}"
LIBCXXABI_GIT_URL="${LIBCXXABI_GIT_URL:-http://git.llvm.org/git/libcxxabi.git}"

ADDITIONAL_LLVM_OPTS=()

if [ "X${LLVM_ENABLE_ASSERTIONS}" = "X1" ]; then
  ADDITIONAL_LLVM_OPTS+=('-DLLVM_ENABLE_ASSERTIONS=ON')
fi

# Setup source tree
mkdir -p "${LLVM_SRC_DIR}"
git clone --depth 1 -b "${LLVM_BRANCH}" "${LLVM_GIT_URL}" "${LLVM_SRC_DIR}"
cd "${LLVM_SRC_DIR}/tools"
git clone --depth 1 -b "${LLVM_BRANCH}" "${CLANG_GIT_URL}" "clang"
cd "${LLVM_SRC_DIR}/projects"
git clone --depth 1 -b "${LLVM_BRANCH}" "${COMPILER_RT_GIT_URL}" "compiler-rt"

# Add libcxx and libcxxabi for macOS only
# Ensures that the freshly built clang can find C++ headers on macOS
if [[ "$OSTYPE" == darwin* ]]; then
  git clone --depth 1 -b "${LLVM_BRANCH}" "${LIBCXX_GIT_URL}" "libcxx"
  git clone --depth 1 -b "${LLVM_BRANCH}" "${LIBCXXABI_GIT_URL}" "libcxxabi"
fi

# Make build tree
mkdir -p "${LLVM_BUILD_DIR}"
cd "${LLVM_BUILD_DIR}"

# Configure
cmake \
  -G "${LLVM_CMAKE_GENERATOR}" \
  -DCMAKE_BUILD_TYPE=${LLVM_BUILD_TYPE} \
  -DLLVM_TARGETS_TO_BUILD=X86 \
  -DLLVM_ENABLE_RTTI=OFF \
  -DLLVM_ENABLE_EH=OFF \
  -DLLVM_ENABLE_LTO=OFF \
  -DLLVM_BUILD_LLVM_DYLIB=OFF \
  -DBUILD_SHARED_LIBS=OFF \
  "${ADDITIONAL_LLVM_OPTS[@]}" \
  "${LLVM_SRC_DIR}"

# Build
if [ "${LLVM_CMAKE_GENERATOR}" = "Ninja" ]; then
  ninja
else
  make -j$(nproc)
fi
