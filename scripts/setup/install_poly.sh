#!/usr/bin/env bash

OPT_DIR_PARAM=$1

# get setup directory path
SETUP_DIR=$(dirname "${BASH_SOURCE[0]}")
SETUP_DIR=$(readlink -f "${SETUP_DIR}")

# find the environment variables
. "${SETUP_DIR}/env.sh" "${OPT_DIR_PARAM}"

##################################################################


# based on HOL4 developers/install-poly.sh
# --------------------------------------------
POLY_BASE="https://github.com/polyml/polyml"
POLY_VERSION="v5.7.1"
POLY_URL=${POLY_BASE}/archive/${POLY_VERSION}.tar.gz

POLY_DIR=${HOLBA_OPT_DIR}/polyml_5_7_1
POLY_DIR_SRC=${HOLBA_OPT_DIR}/polyml_5_7_1_src




##################################################################


# if the output directory exists, we already have a polyml in the cache
if [ -d "${POLY_DIR}" ]; then
  echo "polyml is already available in the cache, exiting."
  exit 0
else
  echo "polyml is not in the cache, downloading it now."
fi

# prepare directories
mkdir "${POLY_DIR_SRC}"
mkdir "${POLY_DIR}"

# download polyml
wget -qO- ${POLY_URL} | \
  tar xvz -C "${POLY_DIR_SRC}" --strip-components 1

# compile polyml
cd "${POLY_DIR_SRC}"
echo "*** Configuring PolyML for prefix: ${POLY_DIR}"
./configure --prefix="${POLY_DIR}"
make

# install polyml to prefix dir
make install

# remove source directory
cd "${HOLBA_OPT_DIR}"
rm -rf "${POLY_DIR_SRC}"

