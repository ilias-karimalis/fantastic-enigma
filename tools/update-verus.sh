#! /bin/bash

set -e

REPOSITORY_ROOT=$(git rev-parse --show-toplevel)

# the verus repository url
VERUS_REPO="https://github.com/verus-lang/verus.git"

# where to clone the repository into
VERUS_DIR="${REPOSITORY_ROOT}/.verus"

# the verus release to be used
# also make sure to update the versions in the workflows actions/cache accordingly!
VERUS_RELEASE="release/0.2025.06.23.2e59154"

NO_BUILD=false
CLEAN=false

for i in "$@"; do
  case $i in
    --no-build)
      NO_BUILD=true
      shift
      ;;
    --verus-release=*)
      VERUS_RELEASE="${i#*=}"
      shift
      ;;
    --clean)
      CLEAN=true
      shift
      ;;
    -*|--*)
      echo "Unknown option $i"
      exit 1
      ;;
    *)
      ;;
  esac
done

if [ "$CLEAN" = true ]; then
  echo "cleaning ${VERUS_DIR}"
  rm -rf "${VERUS_DIR}"
fi

# check if verus repo exists, clone it if needed
if [ ! -d "${VERUS_DIR}" ]; then
    git clone ${VERUS_REPO} "${VERUS_DIR}"
fi

# cd into the verus directory
pushd "${VERUS_DIR}/source"

GIT_STATUS=$(git status)
if [[ $GIT_STATUS == *"${VERUS_RELEASE}"* ]]; then
    echo "Verus repository is already on the right version. No need to update."
else
  # update repository
  git fetch

  # checkout the verus release we want
  git checkout $VERUS_RELEASE

  # print the verus version
  echo "Verus version:   $(git rev-parse HEAD)"

  # delete z3 if it already existed
  rm -rf "$PWD/z3"

  # delete the target directories
  rm -rf "${VERUS_DIR}/source/target-verus"
  rm -rf "${VERUS_DIR}/source/target"
fi

# obtain the z3 binary
if [ ! -f "$PWD/z3" ]; then
  echo "Z3 binary not found, downloading..."
  ./tools/get-z3.sh
else
  echo "Z3 binary already exists."
fi

# check for rustc
rustc --version

# check if we need to build
if [ -f "${VERUS_DIR}/source/target-verus/release/verus" ]; then
  echo "Verus is already built."
else
  if [ "$NO_BUILD" = false ]; then
    echo "Building Verus"

    # activate building
    source ../tools/activate       # for bash and zsh

    # we need to build for no std
    env VERUS_Z3_PATH="$PWD/z3" vargo build --release --vstd-no-std --vstd-no-alloc

    if [ ! -f ${VERUS_DIR}/source/target/release/verusdoc ]; then
      echo "Building verusdoc..."
      vargo build --release -p verusdoc
    fi

    if [ ! -f ${VERUS_DIR}/source/target-verus/release/libvstd.rlib ]; then
      echo "Building vstd..."
      vargo build --release --vstd-no-verify
    fi
  else
      echo "Skipping build"
  fi
fi

popd
