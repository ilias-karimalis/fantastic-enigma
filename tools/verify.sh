#! /bin/bash

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)

# make sure the path etc is set up correctly
source "${REPOSITORY_ROOT}/tools/activate.sh"

# display the commands
set -x

# run verus
verus --crate-type=lib $* "${REPOSITORY_ROOT}/osmosis/src/lib.rs"
