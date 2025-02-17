#!/bin/sh

COMPILE_JS="./build/mi compile --test --disable-prune-utests --to-js --js-target node"
RUN_JS="node"
RUN_MI="./build/boot eval"
TEST_MI="./build/mi run --test --disable-prune-warning"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

compile_test() {
	file=$1
	dbg_info=$2
	set +e
	if [ $dbg_info = true ]; then echo "Compiling $file ..."; fi
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
	echo $($RUN_JS "$filename.js" 2>&1) > "$filename.node.out"
	echo $($RUN_MI "$filename.mc" 2>&1) > "$filename.mi.out"
	diff_output=$(diff "$filename.node.out" "$filename.mi.out" 2>&1)
	exit_code=$?
	rm "$filename.node.out" "$filename.mi.out" "$filename.js"
	set -e
	if [ $exit_code -eq 0 ]
	then
		printf "> Test $file: ${GREEN}PASSED${NC}\n"
	else
		printf "> Test $file: ${RED}FAILED${NC}\n"
		echo "Diff output (node | boot):"
		echo "$diff_output"
		exit 1
	fi
}

clean_tests() {
	rm -rf test/js/*.js
}

clean_out() {
	rm -rf test/js/*.out
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
	clean)
		clean_tests
		;;
esac
