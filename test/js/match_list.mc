include "string.mc"
include "common.mc"

mexpr
	let s = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] in
  match s with [h] ++ t then
    printLn (int2string h)
  else match s with [1, x, _] ++ mid ++ [y, 5] then
    printLn (int2string x);
    printLn (int2string y)
  else match s with rest ++ [a, b] then
    printLn (int2string a);
    printLn (int2string b)
  else
    printLn "nothing"
