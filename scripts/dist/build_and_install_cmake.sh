#!/bin/bash

# This script builds and installs CMake
set -x
set -e
set -o pipefail
: ${CMAKE_SRC_DIR?"CMAKE_SRC_DIR must be specified"}
: ${CMAKE_INSTALL?"CMAKE_INSTALL must be specified"}

# Set values if not already set externally
CMAKE_GENERATOR="${CMAKE_CMAKE_GENERATOR:-Ninja}"
CMAKE_VERSION="${CMAKE_VERSION:-3.8.2}"
CMAKE_TARBALL_URL="${CMAKE_TARBALL_URL:-https://cmake.org/files/v3.8/cmake-${CMAKE_VERSION}.tar.gz}"


# Setup source tree
mkdir -p "${CMAKE_SRC_DIR}"
cd "${CMAKE_SRC_DIR}"
curl -L "${CMAKE_TARBALL_URL}" -o "cmake-${CMAKE_VERSION}.tar.gz"
tar -xvf "cmake-${CMAKE_VERSION}.tar.gz"
cd "cmake-${CMAKE_VERSION}"
# Do a bootstrap so that we don't require CMake to be already installed
./bootstrap --parallel=$(nproc)
make -j$(nproc)

if [ "X${CMAKE_INSTALL}" = "X1" ]; then
  sudo make install
fi
