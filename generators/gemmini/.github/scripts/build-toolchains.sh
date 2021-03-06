#!/bin/bash

#-------------------------------------------------------------
# create the riscv tools binaries from ucb-bar/chipyard with rocket-chip hash given by riscv-boom
#
# run location: circle ci docker image
# usage:
#   $1 - name of the toolchain to build
#-------------------------------------------------------------

# turn echo on and error on earliest command
set -ex

# get shared variables
SCRIPT_DIR="$( cd "$( dirname "$0" )" && pwd )"
source $SCRIPT_DIR/defaults.sh

INSTALL_DIR="$HOME/$1-install"

if [ ! -d "$INSTALL_DIR" ]; then
    cd $HOME

    git clone --progress --verbose https://github.com/ucb-bar/chipyard.git chipyard
    cd $LOCAL_CHIPYARD_DIR

    echo "Checking out Chipyard version: $(cat $LOCAL_CHECKOUT_DIR/CHIPYARD.hash)"
    git fetch
    git checkout $(cat $LOCAL_CHECKOUT_DIR/CHIPYARD.hash)

    cd $HOME

    # init all submodules including the tools (doesn't use CI_MAKE_PROC due to mem. constraints)
    CHIPYARD_DIR="$LOCAL_CHIPYARD_DIR" NPROC=$CI_MAKE_NPROC $LOCAL_CHIPYARD_DIR/scripts/build-toolchains.sh esp-tools
fi

