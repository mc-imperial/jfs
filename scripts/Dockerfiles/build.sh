#!/bin/bash
set -e
set -x
SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../../" ; echo $PWD)"

BASE_TAG="jfs_build_base:ubuntu1604"
FINAL_TAG="jfs_build:ubuntu1604"

# Build base that we can use for other tools
docker build -t "${BASE_TAG}" - < "${SCRIPT_DIR}/jfs_base_ubuntu_16.04.Dockerfile"

docker build --build-arg BASE_IMAGE="${BASE_TAG}" -t "${FINAL_TAG}" -f "${SCRIPT_DIR}/jfs_build_ubuntu_16.04.Dockerfile" "${ROOT_DIR}"

# TODO: Should squash image
