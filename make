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

export BOOT_NAME=boot

# Setup environment variable to find standard library
cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

# General function for building the project
build() {
    mkdir -p build
    dune build
    cp -f _build/install/default/bin/boot.mi build/$BOOT_NAME
}

# Install the boot interpreter locally for the current user
install() {
    bin_path=$HOME/.local/bin/
    lib_path=$HOME/.local/lib/mcore/stdlib
    mkdir -p $bin_path $lib_path
    cp -f build/$BOOT_NAME $bin_path/$BOOT_NAME; chmod +x $bin_path/$BOOT_NAME
    rm -rf $lib_path; cp -rf stdlib $lib_path
    dune install
}

# Run the test suite for parallel programming
runtests_par() {
    (cd test
     ../build/$BOOT_NAME test multicore/*)
    build/$BOOT_NAME test stdlib/multicore/*
}

# Run the test suite for sundials
runtests_sundials() {
    (cd test
     ../build/$BOOT_NAME test sundials/*)
    build/$BOOT_NAME test stdlib/sundials/*
}

# Run the test suite for python intrinsic tests
runtests_py() {
    (cd test
     ../build/$BOOT_NAME test py/*)
}

# Run the test suite for OCaml compiler
runtests_ocaml() {
    (cd stdlib
     ../build/$BOOT_NAME test ocaml/*)
}

# Run the test suite
runtests() {
    (cd test
    ../build/$BOOT_NAME test mexpr &
    ../build/$BOOT_NAME test mlang &
    cd ../stdlib
    ../build/$BOOT_NAME test mexpr &
    ../build/$BOOT_NAME test c &
    ../build/$BOOT_NAME test ad &
    ../build/$BOOT_NAME test ext &
    ../build/$BOOT_NAME test parser &
    cd ..
    export MCORE_STDLIB='@@@'
    build/$BOOT_NAME test stdlib &)
    if [ -n "$MI_TEST_PAR" ]; then
        runtests_par &
    fi
    if [ -n "$MI_TEST_PYTHON" ]; then
        runtests_py &
    fi
    if [ -n "$MI_TEST_SUNDIALS" ]; then
        runtests_sundials &
    fi
    if [ -n "$MI_TEST_OCAML" ]; then
        runtests_ocaml &
    fi
    wait
}

# Lint ocaml source code
lint () {
    dune build @fmt
}

# lints and then fixes ocaml source code
fix () {
    dune build @fmt --auto-promote
}

case $1 in
    lint)
        lint
        ;;
    fix)
        fix
        ;;
    test)
        build
        runtests
        ;;
    test-all)
        export MI_TEST_PYTHON=1
        export MI_TEST_OCAML=1
        export MI_TEST_PAR=1
        lint
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
