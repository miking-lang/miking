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

BOOT_NAME=boot
MI_NAME=mi

BIN_PATH=$HOME/.local/bin
LIB_PATH=$HOME/.local/lib/mcore

# Setup environment variable to find standard library
export MCORE_STDLIB=`pwd`/stdlib

# Compile and build the boot interpreter
build_boot(){
    dune build
    mkdir -p build
    cp -f _build/install/default/bin/boot build/$BOOT_NAME
}

install_boot(){
    dune install > /dev/null 2>&1
}

# Bootstrap the Miking compiler
bootstrap_mi() {
    time build/$BOOT_NAME eval src/main/mi.mc -- compile --disable-optimizations src/main/mi.mc
    mv -f $MI_NAME build/$MI_NAME
}

# Compile a new version of the compiler using the current one
build_mi() {
    if [ -e build/$MI_NAME ]
    then
        time build/$MI_NAME compile src/main/mi.mc
        mv -f $MI_NAME build/$MI_NAME
    else
        echo "No existing compiler binary was found."
        echo "Try running the bootstrapping phase first!"
    fi
}

# Build the Miking compiler
build() {
    if [ -e build/$MI_NAME ]
    then
        echo "Bootstrapped compiler already exists. Run 'make clean' before to recompile. "
    else
        echo "Bootstrapping the Miking compiler (1st round, might take a few minutes)"
        bootstrap_mi
        echo "Bootstrapping the Miking compiler (2nd round, might take some more time)"
        build_mi
    fi
}

# Install the Miking compiler
install() {
    if [ -e build/$MI_NAME ]; then
        set +e; rm -rf $LIB_PATH/stdlib; set -e
        mkdir -p $BIN_PATH $LIB_PATH
        cp -rf stdlib $LIB_PATH
        cp -f build/$MI_NAME $BIN_PATH
    else
        echo "No existing compiler binary was found."
        echo "Try compiling the project first!"
    fi
}

# Lint ocaml source code
lint () {
    dune build @fmt
}

# lints and then fixes ocaml source code
fix () {
    dune build @fmt --auto-promote
}

compile_test () {
  set +e
  output=$1
  output="$output\n$($2 $1 2>&1)"
  if [ $? -eq 0 ]
  then
    binary=$(basename "$1" .mc)
    output="$output$(./$binary)"
    rm $binary
  fi
  echo "$output\n"
  set -e
}

run_test() {
  set +e
  output=$1
  output="$output\n$(build/boot eval src/main/mi.mc -- run --test $1 2>&1)\n"
  output="$output\n$(build/mi run --test $1)\n"
  echo $output
  set -e
}

case $1 in
    boot)
        build_boot
        ;;
    install-boot)
        install_boot
        ;;
    build-mi)
        build_mi
        ;;
    run-test)
        run_test "$2"
        ;;
    compile-test)
        compile_test "$2" "$3"
        ;;
    lint)
        lint
        ;;
    fix)
        fix
        ;;
    install)
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
