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

# General function for building the project
build() {
    declare dune_file="$1"
    (cd src/boot;
     cp "$dune_file" dune
     dune build boot.exe && cp -f _build/default/boot.exe ../../build/boot)
}

# Install the boot interpreter locally for the current user
install() {
    bin_path=$HOME/.local/bin/
    lib_path=$HOME/.local/lib/mcore/stdlib
    mkdir -p $bin_path $lib_path
    cp -f build/boot $bin_path/miking; chmod +x $bin_path/miking
    rm -rf $lib_path; cp -rf stdlib $lib_path
}

# Run the test suite
runtests() {
    (cd test
    ../build/boot test mexpr
    ../build/boot test mlang
    ../build/boot test ext
    cd ../stdlib
    ../build/boot test mexpr
    cd ..
    export MCORE_STDLIB='@@@'
    build/boot test stdlib)
}

# Run the test suite including external functions tests
runtests_ext() {
    runtests
    (cd test
     ../build/boot test ext/*)
    build/boot test stdlib/ext/*
}

case $1 in
    # with external functions integration
    externals-test)
        build dune-boot-ext
        runtests_ext
        ;;
    externals-install)
        build dune-boot-ext
        install
        ;;
    externals)
        build dune-boot-ext
        ;;
    # without external dependencies
    test)
        build dune-boot
        runtests
        ;;
    install)
        build dune-boot
        install
        ;;
    clean)
        rm -rf src/boot/_build
        rm -f build/boot
        ;;
    all | *)
        build dune-boot
        ;;
esac
