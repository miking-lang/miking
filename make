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

# Compile and build the boot interpreter
build_boot(){
    mkdir -p build
    dune build
    cp -f _build/install/default/bin/boot.mi build/$BOOT_NAME
}


# General function for building the project
build() {
    build_boot
    dune install > /dev/null 2>&1
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
    if [ -e build/$BOOT_NAME ]; then
      cp -f build/$BOOT_NAME $bin_path/$BOOT_NAME; chmod +x $bin_path/$BOOT_NAME
    fi
    if [ -e build/$MI_NAME ]; then
      cp -f build/$MI_NAME $bin_path/$MI_NAME; chmod +x $bin_path/$MI_NAME
    fi
    rm -rf $lib_path; cp -rf stdlib $lib_path
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
