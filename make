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
    (cd src/preboot; dune build boot.exe && cp -f _build/default/boot.exe ../../build/preboot)
}

case $1 in
    # Run the test suite
    test)
        buildboot
        cd test
        ../build/preboot test mcore && ../build/preboot tytest tymcore && ../build/preboot parsetest parse
        ;;
    # Clean up the project
    clean)
        rm -rf src/preboot/_build
        rm -f build/preboot
        ;;
    # Just make the project
    all | *)
        buildboot
        ;;
esac
