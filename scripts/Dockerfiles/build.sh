#!/bin/bash
set -e
set -x
SCRIPT_DIR="$( cd ${BASH_SOURCE[0]%/*} ; echo $PWD )"
ROOT_DIR="$(cd "${SCRIPT_DIR}/../../" ; echo $PWD)"

BASE_TAG="jfs_build_base:ubuntu1604"
FINAL_TAG="jfs_build:ubuntu1604"

# Build base that we can use for other tools
docker build -t "${BASE_TAG}" - < "${SCRIPT_DIR}/jfs_base_ubuntu_16.04.Dockerfile"

DOCKER_MAJOR_VERSION=$(docker --version | sed 's/^Docker version \([0-9]\+\)\.\([0-9]\+\).*$/\1/')
DOCKER_MINOR_VERSION=$(docker --version | sed 's/^Docker version \([0-9]\+\)\.\([0-9]\+\).*$/\2/')
DOCKER_BUILD_FILE="${SCRIPT_DIR}/jfs_build_ubuntu_16.04.Dockerfile"

BUILD_OPTS=()
if [ "${DOCKER_MAJOR_VERSION}${DOCKER_MINOR_VERSION}" -lt 1705 ]; then
  # Workaround limitation in older Docker versions where the FROM
  # command cannot be parameterized with an ARG.
  sed \
    -e '/^ARG BASE_IMAGE/d' \
    -e 's/${BASE_IMAGE}/'"${BASE_TAG}/" \
    "${DOCKER_BUILD_FILE}" > "${DOCKER_BUILD_FILE}.patched"
  DOCKER_BUILD_FILE="${DOCKER_BUILD_FILE}.patched"
else
  # This feature landed in Docker 17.05
  # See https://github.com/moby/moby/pull/31352
  BUILD_OPTS+=( \
    "--build-arg" \
    "BASE_IMAGE=${BASE_TAG}" \
  )
fi

if [ -n "${BUILD_CPU_SETS}" ]; then
  BUILD_OPTS+=( \
    "--cpuset-cpus" \
    "${BUILD_CPU_SETS}" \
  )
fi

docker build \
  -t "${FINAL_TAG}" \
  -f "${DOCKER_BUILD_FILE}" \
  "${BUILD_OPTS[@]}" \
  "${ROOT_DIR}"

# Run tests. We do this separate from the build because
# we need SYS_PTRACE which we can't set via `docker build`.
# NOTE: SYS_PTRACE is required by LSan. We use it
# when using the asanified runtime.
# See: https://github.com/google/sanitizers/issues/764
docker run \
  --rm \
  --cap-add SYS_PTRACE \
  "${FINAL_TAG}" \
  "/bin/bash" \
  "/home/user/jfs/src/scripts/dist/test_jfs.sh"


# TODO: Should squash image
