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
MI_LITE_NAME=mi-lite
MI_TMP_NAME=mi-tmp

BIN_PATH=$HOME/.local/bin
LIB_PATH=$HOME/.local/lib/mcore

# Setup environment variable to find standard library
# (and set test namespace for testing)
export MCORE_LIBS=stdlib=`pwd`/stdlib:test=`pwd`/test

# Setup dune/ocamlfind to use local boot library when available
export OCAMLPATH=`pwd`/build/lib

# Compile and build the boot interpreter
build_boot(){
    dune build
    dune install --prefix=build --bindir=`pwd`/build > /dev/null 2>&1
}

install_boot(){
    dune install > /dev/null 2>&1
}

# Compile a new version of the compiler using the current one
build_mi() {
    if [ -e build/$MI_NAME ]
    then
        time build/$MI_NAME compile src/main/mi.mc
        mv -f $MI_NAME build/$MI_TMP_NAME
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
        time build/$BOOT_NAME eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc ./$MI_LITE_NAME
        echo "Bootstrapping the Miking compiler (2nd round, might take some more time)"
        time ./$MI_LITE_NAME 1 src/main/mi.mc ./$MI_NAME
        echo "Bootstrapping the Miking compiler (3rd round, might take some more time)"
        time ./$MI_NAME compile src/main/mi.mc
        mv -f $MI_NAME build/$MI_NAME
        rm -f $MI_LITE_NAME
    fi
}

# As build(), but skips the third bootstrapping step
lite() {
    if [ -e build/$MI_NAME ]
    then
        echo "Bootstrapped compiler already exists. Run 'make clean' before to recompile. "
    else
        echo "Bootstrapping the Miking compiler (1st round, might take a few minutes)"
        time build/$BOOT_NAME eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc ./$MI_LITE_NAME
        echo "Bootstrapping the Miking compiler (2nd round, might take some more time)"
        time ./$MI_LITE_NAME 1 src/main/mi.mc ./$MI_NAME
        mv -f $MI_NAME build/$MI_NAME
        rm -f $MI_LITE_NAME
    fi
}


# Install the Miking compiler
install() {
    if [ -e build/$MI_NAME ]; then
        rm -rf $LIB_PATH/stdlib
        mkdir -p $BIN_PATH $LIB_PATH
        cp -rf stdlib $LIB_PATH
        cp -f build/$MI_NAME $BIN_PATH
    else
        echo "No existing compiler binary was found."
        echo "Try compiling the project first!"
    fi
}

# Uninstall the Miking bootstrap interpreter and compiler
uninstall() {
    set +e
    dune uninstall > /dev/null 2>&1
    rm -f $BIN_PATH/$MI_NAME
    rm -rf $LIB_PATH/stdlib
    set -e
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
  binary=$(mktemp)
  output=$1
  compile="$2 --output $binary"
  output="$output\n$($compile $1 2>&1)"
  exit_code=$?
  if [ $exit_code -eq 0 ]
  then
    output="$output$($binary)"
    exit_code=$?
    rm $binary
    if [ $exit_code -ne 0 ]
    then
        echo "ERROR: the compiled binary for $1 exited with $exit_code"
        exit 1
    fi
  else
    echo "ERROR: command '$compile $1 2>&1' exited with $exit_code"
    rm $binary
    exit 1
  fi
  echo "$output\n"
  set -e
}

run_test_prototype() {
  set +e
  output=$2
  output="$output\n$($1 $2 2>&1)\n"
  echo $output
  set -e
}

run_test() {
  run_test_prototype "build/mi run --test --disable-prune-warning" $1
}

run_test_boot() {
  run_test_prototype "build/boot eval src/main/mi.mc -- run --test --disable-prune-warning" $1
}

run_js_test() {
  ./test/js/make.sh run-test-quiet $1
}

run_js_web_test() {
  ./test/js/web/make.sh run-test-quiet $1
}

case $1 in
    boot)
        build_boot
        ;;
    lite)
        lite
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
    run-test-boot)
        run_test_boot "$2"
        ;;
    compile-test)
        compile_test "$2" "$3"
        ;;
    run-js-test)
        run_js_test "$2"
        ;;
    run-js-web-test)
        run_js_web_test "$2"
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
    uninstall)
        uninstall
        ;;
    clean)
        rm -rf _build
        rm -rf build
        ;;
    all | *)
        build
        ;;
esac
