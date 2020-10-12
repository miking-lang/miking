#!/bin/sh
###################################################
#  Miking is licensed under the MIT license.
#  Copyright (C) David Broman. See file LICENSE.txt
#
#  To make the build system platform independent,
#  building is done using Dune and called from
#  this bash script (on UNIX platforms) or
#  using make.bat (on Windows).
###################################################

# Forces the script to exit on error
set -e

# Setup environment variable to find standard library
cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

# General function for building the project
build() {
    mkdir -p build
    dune build
    cp -f _build/install/default/bin/boot.mi build/mi
}

# Install the boot interpreter locally for the current user
install() {
    bin_path=$HOME/.local/bin/
    lib_path=$HOME/.local/lib/mcore/stdlib
    mkdir -p $bin_path $lib_path
    cp -f build/mi $bin_path/mi; chmod +x $bin_path/mi
    rm -rf $lib_path; cp -rf stdlib $lib_path
}

# Run the test suite for sundials
runtests_sundials() {
    (cd test
     ../build/mi test sundials/*)
    build/mi test stdlib/sundials/*
}

# Run the test suite for python intrinsic tests
runtests_py() {
    (cd test
     ../build/mi test py/*)
}

# Run the test suite for OCaml compiler
runtests_ocaml() {
    (cd stdlib
     ../build/mi test ocaml/*)
}

# Run the test suite
runtests() {
    (cd test
    ../build/mi test mexpr
    ../build/mi test mlang
    cd ../stdlib
    ../build/mi test mexpr
    ../build/mi test ad
    ../build/mi test ext
    cd ..
    export MCORE_STDLIB='@@@'
    build/mi test stdlib)
    if [ -n "$MI_TEST_PYTHON" ]; then
        runtests_py
    fi
    if [ -n "$MI_TEST_SUNDIALS" ]; then
        runtests_sundials
    fi
    if [ -n "$MI_TEST_OCAML" ]; then
        runtests_ocaml
    fi
}

case $1 in
    test)
        build
        runtests
        ;;
    test-all)
        export MI_TEST_PYTHON=1
        export MI_TEST_SUNDIALS=1
        build
        runtests
        ;;
    install)
        build
        install
        ;;
    clean)
        rm -rf _build
        rm -rf build
        ;;
    all | *)
        build
        ;;
esac
