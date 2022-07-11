include "common.mc"
include "string.mc"

mexpr
  printLn (int2string (addi 5 6));
  printLn (int2string (addi 5 (negi 6)));
  ()
