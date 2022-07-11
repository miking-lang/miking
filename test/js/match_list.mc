include "string.mc"
include "common.mc"

mexpr
	let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] in

  match s with [x, y, _] ++ mid ++ [_, z, _] then
    dprintLn x;
    dprintLn y;
    -- dprintLn mid; -- Should be [3, 4, 5, 6] BREAKS TESTS
    dprintLn z;
    0
  else match s with [h] ++ t then
    dprintLn h;
    dprintLn t;
    1
  else match s with rest ++ [a, b] then
    dprintLn a;
    dprintLn b;
    dprintLn rest;
    2
  else match s with [a, b, c] then
    dprintLn a;
    dprintLn b;
    dprintLn c;
    3
  else
    printLn "nothing";
    4
