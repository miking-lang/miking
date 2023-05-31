#!/bin/sh

COMPILE_JS="./build/boot eval src/main/mi.mc -- compile --test --disable-prune-utests --to-js --js-target web"
RUN_JS="node test/js/web/test_runner.js"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

install_deps() {
	PREV_PWD=$PWD
	cd test/js/web
	set +e
	output=$(npm install 2>&1)
	exit_code=$?
	set -e
	if [ $exit_code -ne 0 ]
	then
		echo "$output"
		echo "npm ERROR: Installing JavaScript web test dependencies failed!"
		exit 1
	fi
	cd $PREV_PWD
}

compile_test() {
	file=$1
	dbg_info=$2
	set +e
	if [ $dbg_info = true ]; then echo "Compiling $file ..."; fi
	install_deps
	output=$($COMPILE_JS $file 2>&1)
	exit_code=$?
	if [ $dbg_info = true ]; then echo "$output"; fi
	set -e
	if [ $exit_code -ne 0 ]
	then
		echo "ERROR: Compiling test $file failed!"
		exit 1
	fi
}

run_test() {
	file=$1
	dbg_info=$2
	compile_test $file $dbg_info
	set +e
	filename=${file%.*}
	jsfile="$filename.js"
	output=$($RUN_JS $jsfile 2>&1)
  	exit_code=$?
	set -e
	rm $jsfile # remove the generated file
	if [ $dbg_info = true ]; then echo "$output"; fi
	if [ $exit_code -eq 0 ]
	then
		printf "> Test $file: ${GREEN}PASSED${NC}\n"
	else
		printf "> Test $file: ${RED}FAILED${NC}\n"
		exit 1
	fi
}


case $1 in
	compile-test)
		compile_test "$2" true
		;;
	run-test)
		run_test "$2" true
		;;
	run-test-quiet)
		run_test "$2" false
		;;
esac
