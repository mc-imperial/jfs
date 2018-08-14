# This file should be sourced to update
# the environment with sanitizer suppressions
set -x
SUPPRESSIONS_ROOT_DIR="$(cd "${BASH_SOURCE[0]%/*}" && pwd )"
if [ -d "${SUPPRESSIONS_ROOT_DIR}" ]; then
  export LSAN_OPTIONS="suppressions=${SUPPRESSIONS_ROOT_DIR}/lsan/lsan_sup.txt"
  export UBSAN_OPTIONS="suppressions=${SUPPRESSIONS_ROOT_DIR}/ubsan/ubsan_sup.txt,halt_on_error=1"
else
 echo "SUPPRESSIONS_ROOT_DIR \"${SUPPRESSIONS_ROOT_DIR}\" is invalid"
fi
set +x
