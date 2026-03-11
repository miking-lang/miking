include "common.mc"
include "string.mc"

mexpr
	let l = [1, 2, 3, 4, 5] in
  printLn (int2string (foldl addi 0 l))
