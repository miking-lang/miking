COMPILE_EXTREC="./build/mi-tmp compile --test --experimental-records"

TEST_LOCATION="test/extrec/"
TYPELOG_LOCATION="test/extrec/typelog/"

TYPE_TEST_LOCATION="test/extrec/ill-typed/"

OUTPUT_LOCATION="test/extrec/out"

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

run_test_csv() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo -n "$input_file,"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TEST_LOCATION$input_file 2> /dev/null > /dev/null
  if [ $? -eq 0 ] 
  then
    echo -n "\testpass,"
    ./$OUTPUT_LOCATION/$file_prefix > /dev/null 2> /dev/null
    if [ $? -eq 0 ] 
    then 
      echo "\testpass"
    else 
      echo "\testfail"
    fi
    rm ./$OUTPUT_LOCATION/$file_prefix
  else
    echo "\testfail,\testunknown"
  fi
  set -e
}

all_csv() {
  echo "filename,compilation,evaluation"
  
  for test_file in $TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    run_test_csv $relative_path
  done
}

run_illtyped_test_csv() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo -n "$input_file,"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TYPE_TEST_LOCATION$input_file 2> /dev/null > /dev/null
  if [ $? -ne 0 ] 
  then
    echo "\testpass"
  else
    echo "\testfail"
  fi
  set -e
  rm -f ./$OUTPUT_LOCATION/$file_prefix
}

ill_typed_csv() {
  echo "filename,typeerror"

  for test_file in $TYPE_TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    run_illtyped_test_csv $relative_path
  done
}

run_test() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo "--- $input_file ---"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TEST_LOCATION$input_file > /dev/null
  if [ $? -eq 0 ] 
  then
    printf "${GREEN}Compilation successful!\n${NC}"
    ./$OUTPUT_LOCATION/$file_prefix > /dev/null
    if [ $? -eq 0 ] 
    then 
      printf  "${GREEN}Test Passed}!\n${NC}"
    else 
      printf "${RED}Test or Execution Failed!\n${NC}"

    fi
    rm ./$OUTPUT_LOCATION/$file_prefix
  else
    printf "${RED}Compilation error!\n${NC}"
  fi
  set -e
}

run_all() {
  for test_file in $TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    # echo "$relative_path"
    # echo "$test_file"
    run_test $relative_path
  done
}

run_illtyped_test() {
  input_file=$1
  file_prefix=${input_file%.*}
  set +e

  echo "--- $input_file ---"
  $COMPILE_EXTREC --output $OUTPUT_LOCATION/$file_prefix $TYPE_TEST_LOCATION$input_file 2> /dev/null
  if [ $? -ne 0 ] 
  then
    printf "${GREEN}Type checking fialed as expected!\n${NC}"
  else
    printf "${RED}Compilation succeeded even though the program should not have been well-typed!\n${NC}"
  fi
  set -e
  rm -f ./$OUTPUT_LOCATION/$file_prefix
}

run_all_illtyped() {
    for test_file in $TYPE_TEST_LOCATION*.mc 
  do
    relative_path=$(basename $test_file)
    run_illtyped_test $relative_path
  done
}

generate_type_log() {
  for test_file in $TYPELOG_LOCATION*.mc 
  do 
    echo "=== $test_file ==="
    $COMPILE_EXTREC --output typelog $test_file 2> /dev/null > /dev/null
    ./typelog
    rm -f typelog
  done
}

run_stdlib() {
  for file in "stdlib/"*.mc
  do
    echo "=== $file ==="
    $COMPILE_EXTREC --output $OUTPUT_LOCATION/stdlib $file > /dev/null 2> /dev/null
    if [ $? -eq 0 ] 
    then
      printf "${GREEN}Compilation successful!\n${NC}"
      ./$OUTPUT_LOCATION/stdlib > /dev/null 2> /dev/null
      if [ $? -eq 0 ] 
      then 
        printf  "${GREEN}Test Passed}!\n${NC}"
      else 
        printf "${RED}Test or Execution Failed!\n${NC}"
      fi
    else
      printf "${RED}Compilation error!\n${NC}"
    fi
    rm -f ./$OUTPUT_LOCATION/stdlib
  done
}

run_patterns() {
  for file in "test/extrec/pattern-tests/"*.mc
  do
    echo "=== $file ==="
    if [[ $file == *.err.mc ]]; then
      $COMPILE_EXTREC --output $OUTPUT_LOCATION/patterns $file > /dev/null 2> /dev/null
      if [ $? -ne 0 ] 
      then
        printf "${GREEN}Compilation failed as expected!\n${NC}"
      else
        printf "${RED}Compilation succeeded even though the program should not have been well-typed!\n${NC}"
      fi
    else    
      $COMPILE_EXTREC --output $OUTPUT_LOCATION/patterns $file > /dev/null 2> /dev/null
      if [ $? -eq 0 ] 
      then
        printf "${GREEN}Compilation successful!\n${NC}"
        ./$OUTPUT_LOCATION/patterns > /dev/null 2> /dev/null
        if [ $? -eq 0 ] 
        then 
          printf  "${GREEN}Test Passed!\n${NC}"
        else 
          printf "${RED}Test or Execution Failed!\n${NC}"
        fi
      else
        printf "${RED}Compilation error!\n${NC}"
      fi
      rm -f ./$OUTPUT_LOCATION/patterns
    fi
  done
}

case $1 in 
  run-test)
    run_test "$2"
    ;;
  run-all)
    run_all
    run_all_illtyped
    ;;
  run-type-test)
    run_illtyped_test "$2"
    ;;
  run-all-type)
    run_all_illtyped
    ;;
  all-csv)
    all_csv
    ;;
  type-csv)
    ill_typed_csv
    ;;
  stdlib)
    run_stdlib
    ;;
  patterns) 
    run_patterns
    ;;
  type-log)
    generate_type_log "$2"
    ;;
  *)
    echo "Unknown command! Use 'run-all' or 'run-test <filename>'!"
    exit 1
    ;;
esac
