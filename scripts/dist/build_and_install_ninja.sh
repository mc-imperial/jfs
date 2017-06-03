#!/bin/bash

# This script builds and installs ninja
set -x
set -e
set -o pipefail
: ${NINJA_SRC_DIR?"NINJA_SRC_DIR must be specified"}
: ${NINJA_INSTALL?"NINJA_INSTALL must be specified"}

# Set values if not already set externally
NINJA_VERSION="${NINJA_VERSION:-1.7.2}"
NINJA_TARBALL_URL="${NINJA_TARBALL_URL:-https://github.com/ninja-build/ninja/archive/v${NINJA_VERSION}.tar.gz}"

# Setup source tree
mkdir -p "${NINJA_SRC_DIR}"
cd "${NINJA_SRC_DIR}"
curl -L "${NINJA_TARBALL_URL}" -o "v${NINJA_VERSION}.tar.gz"
tar -xvf "v${NINJA_VERSION}.tar.gz"
cd "ninja-${NINJA_VERSION}"
./configure.py --bootstrap

if [ "X${NINJA_INSTALL}" = "X1" ]; then
  sudo install ninja /usr/bin/
fi
