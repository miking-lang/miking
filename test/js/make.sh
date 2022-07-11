#!/usr/bin/bash

COMPILE_JS="./build/boot eval src/main/mi.mc -- compile --to-js"
RUN_JS="node"
RUN_MI="./build/boot eval"
TEST_MI="./build/mi run --test --disable-prune-warning"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

compile_test() {
	set +e
	echo "Compiling $1 ..."
	output=$($COMPILE_JS $1 2>&1)
	echo "$output\n"
	set -e
	if [ $? -ne 0 ]
	then
		echo "ERROR: Compiling test $1 failed!"
		exit 1
	fi
}

run_test() {
	compile_test $1
	set +e
	filename=${1%.*}
	node_output=$($RUN_JS "$filename.js" 2>&1)
	mi_output=$($RUN_MI "$filename.mc" 2>&1)
	diff_output=$(diff -y <(echo "$node_output") <(echo "$mi_output") 2>&1)
  	exit_code=$?
	set -e
	if [ $exit_code -eq 0 ]
	then
		printf "> Test $1: ${GREEN}PASSED${NC}\n"
	else
		printf "> Test $1: ${RED}FAILED${NC}\n"
		echo "Diff output:"
		echo "$diff_output"
		exit 1
	fi
}

run_all_tests() {
	echo "Running all tests ..."
	for test in test/js/*.mc; do
		[ -f "$test" ] || break
		run_test $test
	done
}

clean_tests() {
	echo "Cleaning"
	rm -rf test/js/*.js
}

case $1 in
	compile-test)
		compile_test "$2"
		;;
	run-test)
		run_test "$2"
		clean_tests
		;;
	run-all)
		run_all_tests
		clean_tests
		;;
	clean)
		clean_tests
		;;
esac
