include "string.mc"
include "common.mc"

mexpr
	let s = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] in
  -- let printInt = lam x. printLn (int2string x) in
  -- let printSeq = lam x. printLn (seq2string int2string x) in
  -- let printSeqSeq = lam x. printLn (seq2string (seq2string int2string) x) in

  (match s with [x, y, _] ++ mid ++ [_, z, _] then
    printLn (int2string x);
    printLn (int2string y);
    -- printLn (seq2string int2string mid); -- Should be [3, 4, 5, 6] BREAKS TESTS
    printLn (int2string z);
    0
  else match s with [h] ++ t then
    printLn (int2string h);
    -- printLn (seq2string int2string t);
    1
  else match s with rest ++ [a, b] then
    printLn (int2string a);
    printLn (int2string b);
    -- printLn (seq2string int2string rest);
    2
  else match s with [a, b, c] then
    printLn (int2string a);
    printLn (int2string b);
    printLn (int2string c);
    3
  else 4);

  (let u = [ [0, 1, 2], [3, 4, 5], [6, 7, 8] ] in
  match u with [ [hd] ++ tl ] ++ rest then
    printLn (int2string hd);
    -- printLn (seq2string int2string tl);
    5
  else match u with [ [hd, mdl] ++ tl, [last] ] ++ rest then
    printLn (int2string hd);
    printLn (int2string mdl);
    -- printLn (seq2string int2string tl);
    printLn (int2string last);
    -- printSeqSeq rest;
    6
  else
    printLn "nothing";
    7);

  ()
