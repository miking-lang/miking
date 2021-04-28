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
export MI_NAME=mi

# Setup environment variable to find standard library
cd stdlib; export MCORE_STDLIB=`pwd`; cd ..;

# General function for building the project
build() {
    mkdir -p build
    dune build
    dune install > /dev/null 2>&1
    cp -f _build/install/default/bin/boot.mi build/$BOOT_NAME
    if [ -e build/$MI_NAME ]
    then
        echo "Bootstrapped compiler already exists. Run 'make clean' before to recompile. "
    else
        echo "Bootstrapping the Miking compiler (1st round, might take a few minutes)"
        time build/$BOOT_NAME eval src/main/mi.mc -- compile --disable-optimizations src/main/mi.mc
        echo "Bootstrapping the Miking compiler (2nd round, might take some more time)"
        time ./$MI_NAME compile src/main/mi.mc
        mv -f $MI_NAME build/$MI_NAME
        rm -f mi
    fi
}

# Install the boot interpreter locally for the current user
install() {
    bin_path=$HOME/.local/bin/
    lib_path=$HOME/.local/lib/mcore/stdlib
    mkdir -p $bin_path $lib_path
    cp -f build/$BOOT_NAME $bin_path/$BOOT_NAME; chmod +x $bin_path/$BOOT_NAME
    cp -f build/$MI_NAME $bin_path/$MI_NAME; chmod +x $bin_path/$MI_NAME
    rm -rf $lib_path; cp -rf stdlib $lib_path
}

# Run the test suite for parallel programming
runtests_par() {
    (cd test
     ../build/$BOOT_NAME eval multicore/* --test)
    build/$BOOT_NAME eval stdlib/multicore/* --test
}

# Run the test suite for sundials
runtests_sundials() {
    (cd test
     ../build/$BOOT_NAME eval sundials/* --test)
    build/$BOOT_NAME eval stdlib/sundials/* --test
}

# Run the test suite for python intrinsic tests
runtests_py() {
    (cd test
     ../build/$BOOT_NAME eval py/* --test)
}

# Run the test suite for OCaml compiler
runtests_ocaml() {
    (cd stdlib
     ../build/$BOOT_NAME eval ocaml/* --test)
}

# Run the test suite
runtests() {
    (cd test
    ../build/$BOOT_NAME eval mexpr --test &
    ../build/$BOOT_NAME eval mlang --test&
    cd ../stdlib
    ../build/$BOOT_NAME eval mexpr --test &
    ../build/$BOOT_NAME eval c --test &
    ../build/$BOOT_NAME eval ad --test&
    ../build/$BOOT_NAME eval ext --test &
    ../build/$BOOT_NAME eval parser --test&
    cd ..
    export MCORE_STDLIB='@@@'
    build/$BOOT_NAME eval stdlib --test &)
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
