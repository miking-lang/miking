#!/bin/bash
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

BASE_DEPS="batteries str linenoise"

# General function for building the project
build() {
    mkdir -p build
    (cd src/boot;
    DEPS=$BASE_DEPS
    > dune
    if [[ -n $MI_ENABLE_SUNDIALS ]]; then
        DEPS="$DEPS sundialsml"
        echo "(copy_files ext/*)" >> dune
    else
        echo "(copy_files ext-skel/*)" >> dune
    fi
    if [[ -n $MI_ENABLE_PYTHON ]]; then
        DEPS="$DEPS pyml"
        echo "(copy_files py/*)" >> dune
    else
        echo "(copy_files py-skel/*)" >> dune
    fi
    cat >> dune << EndOfMessage

(ocamllex lexer)
(ocamlyacc parser)

(executable
  (name boot)
  (libraries $DEPS)
)
EndOfMessage
    dune build boot.exe && cp -f _build/default/boot.exe ../../build/mi)
}

build_kernel() {
  mkdir -p build
  (cd src/boot;
  cp kernel/dune-kernel dune
  dune build kernel.exe && cp -f _build/default/kernel.exe ../../build/kernel)
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
runtests_ext() {
    (cd test
     ../build/mi test ext/*)
    build/mi test stdlib/ext/*
}

# Run the test suite for python intrinsic tests
runtests_py() {
    (cd test
     ../build/mi test py/*)
}

# Run the test suite
runtests() {
    (cd test
    ../build/mi test mexpr
    ../build/mi test mlang
    ../build/mi test ext
    cd ../stdlib
    ../build/mi test mexpr
    cd ..
    export MCORE_STDLIB='@@@'
    build/mi test stdlib)
    if [[ -n $MI_ENABLE_PYTHON ]]; then
        runtests_py
    fi
    if [[ -n $MI_ENABLE_SUNDIALS ]]; then
        runtests_ext
    fi
}

case $1 in
    test)
        build
        runtests
        ;;
    test-all)
        export MI_ENABLE_PYTHON=1
        export MI_ENABLE_SUNDIALS=1
        build
        runtests
        ;;
    kernel)
        build_kernel
    ;;
    install)
        build
        install
        ;;
    clean)
        rm -rf src/boot/_build
        rm -rf build
        ;;
    all | *)
        build
        ;;
esac
