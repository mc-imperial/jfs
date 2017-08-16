#!/bin/bash
# This script tests JFS
set -x
set -e
set -o pipefail
: ${JFS_SRC_DIR?"JFS_SRC_DIR must be specified"}
: ${JFS_BUILD_DIR?"JFS_BUILD_DIR must be specified"}

# Set values if not already set externally
JFS_CMAKE_GENERATOR="${JFS_CMAKE_GENERATOR:-Ninja}"

cd "${JFS_BUILD_DIR}"

# Test
if [ "${JFS_CMAKE_GENERATOR}" = "Ninja" ]; then
  ninja check
else
  make -j$(nproc) check
fi
