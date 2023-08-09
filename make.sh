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

prefix="${prefix:-$HOME/.local}"
bindir="${bindir:-$prefix/bin}"
libdir="${libdir:-$prefix/lib}"
opamlibdir="${OPAM_SWITCH_PREFIX:+$OPAM_SWITCH_PREFIX/lib}"
ocamllibdir="${ocamllibdir:-${opamlibdir:-$libdir/ocaml/site-lib}}"
mcoredir=$libdir/mcore

# Setup environment variable to find standard library
# (and set test namespace for testing)
export MCORE_LIBS=stdlib=`pwd`/stdlib:test=`pwd`/test

# Setup dune/ocamlfind to use local boot library when available
# Do preserve existing OCAML_PATH to find linenoise et al.
export OCAMLPATH="$(pwd)/build/lib${OCAMLPATH:+:}$OCAMLPATH"

# Compile and build the boot interpreter
build_boot(){
    dune build
    dune install --prefix=build --bindir=`pwd`/build > /dev/null 2>&1
}

install_boot(){
    dune install --prefix=$prefix --libdir=$ocamllibdir > /dev/null 2>&1
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

# Build the Miking compiler.  If $1 is 'lite', skip the last stage.
build() {
    if [ -e build/$MI_NAME ]
    then
        echo "Bootstrapped compiler already exists. Run 'make clean' before to recompile. "
    else
        echo "Bootstrapping the Miking compiler (1st round, might take a few minutes)"
        time build/$BOOT_NAME eval src/main/mi-lite.mc -- 0 src/main/mi-lite.mc ./$MI_LITE_NAME
        echo "Bootstrapping the Miking compiler (2nd round, might take some more time)"
        time ./$MI_LITE_NAME 1 src/main/mi.mc ./$MI_NAME
        if [ "$1" != "lite" ]
        then
            echo "Bootstrapping the Miking compiler (3rd round, might take some more time)"
            time ./$MI_NAME compile src/main/mi.mc
        fi
        mv -f $MI_NAME build/$MI_NAME
        rm -f $MI_LITE_NAME
    fi
}

# Install the Miking compiler
install() {
    if [ -e build/$MI_NAME ]; then
        rm -rf $mcoredir/stdlib
        mkdir -p $bindir $mcoredir
        cp -rf stdlib $mcoredir
        cp -f build/$MI_NAME $bindir
    else
        echo "No existing compiler binary was found."
        echo "Try compiling the project first!"
    fi
}

# Uninstall the Miking bootstrap interpreter and compiler
uninstall() {
    dune uninstall --prefix=$prefix --libdir=$ocamllibdir > /dev/null 2>&1
    rm -f $bindir/$MI_NAME
    rm -rf $mcoredir/stdlib
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
  compile="$2 --output $binary"
  output="$($compile "$1" 2>&1)"
  exit_code=$?
  if [ $exit_code -ne 0 ]
  then
    printf "$1\n$output\nCommand '$compile $1 2>&1' exited with code $exit_code\n\n"
    rm -f $binary
    exit 1
  else
    output="$($binary)"
    exit_code=$?
    rm $binary
    printf "$1\n$output\n\n"
    if [ $exit_code -ne 0 ]; then exit 1; fi
  fi
  set -e
}

run_test() {
  set +e
  output="$1\n$($2 "$1" 2>&1)"
  exit_code=$?
  printf "$output\n\n"
  if [ $exit_code -ne 0 ]; then exit 1; fi
  set -e
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
        build lite
        ;;
    install-boot)
        install_boot
        ;;
    build-mi)
        build_mi
        ;;
    run-test)
        run_test "$2" "$3"
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
