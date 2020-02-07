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
buildboot(){
    (cd src/boot;
     dune build boot.exe && cp -f _build/default/boot.exe ../../build/boot)
}

case $1 in
    # Run the test suite
    test)
        buildboot
        cd test
        ../build/boot test mexpr
        ../build/boot test mlang
        ../build/boot test ext
        cd ../stdlib
        ../build/boot test mexpr
        cd ..
        unset MCORE_STDLIB
        build/boot test stdlib
        ;;
    # Clean up the project
    clean)
        rm -rf src/boot/_build
        rm -f build/boot
        ;;
    # Just make the project
    install)
        buildboot
        install_path=$HOME/.local/bin
        mkdir -p $install_path
        cp -f build/boot $install_path/miking
        chmod +x $install_path/miking
        ;;
    all | *)
        buildboot
        ;;
esac
