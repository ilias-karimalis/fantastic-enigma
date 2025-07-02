# the root of the repository
REPOSITORY_ROOT=$(git rev-parse --show-toplevel)

# where the verus directory is
VERUS_DIR="${REPOSITORY_ROOT}/.verus"

if [ ! -d "${VERUS_DIR}" ]; then
    echo "Verus directory not found. Please run tools/update-verus.sh first."
    exit 1
fi

# setup verus by adding the binary to the path
export PATH="${VERUS_DIR}/source/target-verus/release":$PATH

