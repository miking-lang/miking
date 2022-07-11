include "common.mc"

mexpr
	let l = [1, 2, 3, 4, 5] in
	dprintLn (foldl (addi) 0 l)
