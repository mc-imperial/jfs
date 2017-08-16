#!/bin/bash

# This script builds JFS and its dependencies using Docker and then
# extracts the necessary files and packs them into a tarball suitable
# for Solver submission on StarExec (https://www.starexec.org/)

TEMP_DOCKER_IMAGE_NAME="jfs_starexec_temp"
TEMP_DOCKER_CONTAINER_NAME="jfs_starexec_temp_container"
RM_TEMP_DOCKER_IMAGE="0"
TEMP_DIR="/tmp/jfs-$$"
OUTPUT_FILE_NAME=""
SCRIPT_ROOT=$(cd ${BASH_SOURCE[0]%/*} ; echo $PWD)
REPO_ROOT=$(cd "${SCRIPT_ROOT}/../../" ; echo $PWD)

function usage() {
  echo "$(basename $0) [options] <output_file>"
  echo ""
  echo "<output_file> - The destination path for tarball"
  echo ""
  echo "OPTIONS"
  echo ""
  echo "--help"
  echo "Show help"
  echo ""
  echo "--rm-temp-docker-image"
  echo "Remove temporary docker image when done. Default is to keep it for cache reasons"
  echo ""
  echo "--temp-docker-image-name <name>"
  echo "Specify name for temporary docker image (default \"${TEMP_DOCKER_IMAGE_NAME}\")"
  echo ""
  echo "--temp-docker-container-name <name>"
  echo "Specify name for temporary docker container (default \"${TEMP_DOCKER_CONTAINER_NAME}\")"
  echo ""
  echo "--temp-dir <path>"
  echo "Directory to write temporary files for tarball preparation"
  echo ""
}

if [ "$#" -lt 1 ]; then
  echo "Insufficent number of arguments. See --help"
  exit 1
fi

# Parse args
while [ -n "$1" ]; do
  if [ $# -gt 1 ] || [ $(echo "$1" | grep -Ec '^--help') -eq 1 ] ; then
    # Parse optional args
    case "$1" in
      --help)
        usage
        exit 0
      ;;
      --rm-temp-docker-image)
        RM_TEMP_DOCKER_IMAGE=1
        ;;
      --temp-docker-image-name)
        shift
        TEMP_DOCKER_IMAGE_NAME="$1"
        ;;
      --temp-docker-container-name)
        shift
        TEMP_DOCKER_CONTAINER_NAME="$1"
        ;;
      --temp-dir)
        shift
        TEMP_DIR="$1"
        ;;
      *)
        echo "\"$1\" is not a recognised argument"
        exit 1
    esac
  else
    # Get mandatory arg
    OUTPUT_FILE_NAME="$1"
  fi
  shift
done

PATH_TO_DOCKER_FILE="${SCRIPT_ROOT}/StarExec-SMTCOMP2017.Dockerfile"

# Show settings
echo "OUTPUT_FILE_NAME: ${OUTPUT_FILE_NAME}"
echo "REPO_ROOT: \"${REPO_ROOT}\""
echo "RM_TEMP_DOCKER_IMAGE: ${RM_TEMP_DOCKER_IMAGE}"
echo "SCRIPT_ROOT: \"${SCRIPT_ROOT}\""
echo "TEMP_DIR: ${TEMP_DIR}"
echo "TEMP_DOCKER_CONTAINER_NAME: ${TEMP_DOCKER_CONTAINER_NAME}"
echo "TEMP_DOCKER_IMAGE_NAME: ${TEMP_DOCKER_IMAGE_NAME}"

# Sanity checks
if [ ! -d "${REPO_ROOT}" ]; then
  echo "REPO_ROOT (${REPO_ROOT}) is not a directory"
  exit 1
fi
if [ ! -d "${SCRIPT_ROOT}" ]; then
  echo "SCRIPT_ROOT (${SCRIPT_ROOT}) is not a directory"
  exit 1
fi
if [ ! -e "${PATH_TO_DOCKER_FILE}" ]; then
  echo "PATH_TO_DOCKER_FILE (${PATH_TO_DOCKER_FILE}) does not exist"
  exit 1
fi

function docker_container_exists() {
  if [ -n "$(docker ps --all --filter="name=^/${1}\$" --format='{{.Names}}')" ]; then
    echo 1
  else
    echo 0
  fi
}

set -e
set -x
set -o pipefail

if [ "$(docker_container_exists "${TEMP_DOCKER_CONTAINER_NAME}")" -ne 0 ]; then
  echo "Error: container ${TEMP_DOCKER_CONTAINER_NAME} already exists"
  exit 1
fi

# Build JFS and its dependencies in Docker
docker build \
  -t "${TEMP_DOCKER_IMAGE_NAME}" \
  -f "${PATH_TO_DOCKER_FILE}" \
  "${REPO_ROOT}"

# Run tests
docker run \
  --rm \
  --cap-add SYS_PTRACE \
  "${TEMP_DOCKER_IMAGE_NAME}"
  "/bin/bash"
  "/home/user/jfs/src/scripts/dist/test_jfs.sh"

# Create temporary container than we can extract build artifacts from
docker create --name "${TEMP_DOCKER_CONTAINER_NAME}" "${TEMP_DOCKER_IMAGE_NAME}" /bin/true

# Mkdir temp dir
mkdir -p "${TEMP_DIR}"
mkdir -p "${TEMP_DIR}/bin"

# Copy build artifacts across
artifacts=("bin/jfs")
for a in "${artifacts[*]}" ; do
  docker cp "${TEMP_DOCKER_CONTAINER_NAME}:/home/user/jfs/build/${a}" "${TEMP_DIR}/${a}"
done

# Remove container
docker rm "${TEMP_DOCKER_CONTAINER_NAME}"

if [ "${RM_TEMP_DOCKER_IMAGE}" -eq 1 ]; then
  docker rmi "${TEMP_DOCKER_IMAGE_NAME}"
fi

# Copy across StarExec configurations
cp "${SCRIPT_ROOT}/configs/"* "${TEMP_DIR}/bin"

# Copy across StarExec description
cp "${SCRIPT_ROOT}/starexec_description.txt" "${TEMP_DIR}/"

# Now tarball up
tar -C "${TEMP_DIR}" -cvzf "${OUTPUT_FILE_NAME}" $(cd "${TEMP_DIR}"; echo *)

# Remove temp dir
rm -rf "${TEMP_DIR}"

# Done
