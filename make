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

# General function for building the project
buildboot(){
    (cd src/boot; jbuilder build boot.exe && cp -f _build/default/boot.exe ../../build/boot)
}

case $1 in
    # Old build system using ocamlbuild and ocaml functions. Should be removed in the future.
    old)
        ocaml build/build.ml $2 $3 $4
        ;;
    # Run the test suite
    test)
        buildboot
        cd test
        ../build/boot test mcore ppl ragnar
        ;;
    # Clean up the project
    clean)
        rm -rf src/boot/_build
        rm -f build/boot
        ;;
    # Just make the project
    all | *)
        buildboot
        ;;
esac
