-- Sequences and strings.
--
-- The values are checked with utests; the printing at the end is deliberate,
-- since what reaches the host is its own question: a string has to be
-- marshalled out of the sequence representation, and a float has to be
-- formatted the way the reference backend formats it.
mexpr

-- Strings are ordinary sequences of characters.
utest concat "ab" "cd" with "abcd" in
utest cons 'x' "yz" with "xyz" in
utest snoc "ab" 'c' with "abc" in
utest reverse "abc" with "cba" in
utest subsequence "hello" 1 3 with "ell" in
utest tail "abc" with "bc" in
utest head "abc" with 'a' in
utest length "hello" with 5 in
utest null "" with true in
utest null "a" with false in
utest map (lam c. int2char (addi (char2int c) 1)) "abc" with "bcd" in
utest set "abc" 1 'X' with "aXc" in

-- Miking strings are codepoint sequences. This one is five characters, where
-- a JS string would report six, because the emoji is a surrogate pair there.
-- MCore has no \u escape, so the codepoint is built with int2char.
let emoji = [int2char 128512] in
let mixed = concat "ab" (concat emoji "cd") in
utest length mixed with 5 in
utest char2int (get mixed 2) with 128512 in

-- Sequences of other element types behave the same way.
let s = [1, 2, 3, 4, 5] in
utest length s with 5 in
utest get s 0 with 1 in
utest head s with 1 in
utest tail s with [2, 3, 4, 5] in
utest concat s [6] with [1, 2, 3, 4, 5, 6] in
utest cons 0 s with [0, 1, 2, 3, 4, 5] in
utest snoc s 6 with [1, 2, 3, 4, 5, 6] in
utest reverse s with [5, 4, 3, 2, 1] in
utest subsequence s 1 2 with [2, 3] in
utest create 4 (lam i. i) with [0, 1, 2, 3] in
utest get (create 4 (lam i. muli i 2)) 3 with 6 in
utest (splitAt s 2).0 with [1, 2] in
utest (splitAt s 2).1 with [3, 4, 5] in

-- A sequence is a rope or a list, and every operation keeps the one it was
-- given; only `concat` can change it, and only into a list.
let rope = createRope 3 (lam i. i) in
let list = createList 3 (lam i. i) in
utest isRope s with true in
utest isList s with false in
utest isRope rope with true in
utest isList list with true in
utest isRope (concat rope rope) with true in
utest isList (concat list list) with true in
utest isList (concat list rope) with true in
utest isList (concat rope list) with true in
utest isList (cons 9 list) with true in
utest isList (snoc list 9) with true in
utest isList (tail list) with true in
utest isList (reverse list) with true in
utest isList (map (lam x. x) list) with true in
utest isList (mapi (lam. lam x. x) list) with true in
utest isList (set list 1 9) with true in
utest isList (subsequence list 1 2) with true in
utest isList (splitAt list 1).0 with true in
utest isList (splitAt list 1).1 with true in
utest isRope (create 3 (lam i. i)) with true in

-- The elements survive the representation, whichever it is.
utest list with [0, 1, 2] in
utest length list with 3 in
utest get list 2 with 2 in
utest head list with 0 in
utest reverse list with [2, 1, 0] in
utest snoc list 7 with [0, 1, 2, 7] in
utest cons 7 list with [7, 0, 1, 2] in
utest set list 1 7 with [0, 7, 2] in
utest concat list rope with [0, 1, 2, 0, 1, 2] in
utest concat rope list with [0, 1, 2, 0, 1, 2] in
utest null (createList 0 (lam i. i)) with true in
utest null list with false in
utest foldl (lam acc. lam x. addi acc x) 0 list with 3 in
utest foldr (lam x. lam acc. addi x acc) 0 list with 3 in
utest subsequence list 1 2 with [1, 2] in
utest mapi (lam i. lam x. addi i x) list with [0, 2, 4] in

-- Walking a list with an edge pattern, the way a list is meant to be used.
recursive let sum = lam acc. lam xs.
  match xs with [a] ++ rest then sum (addi acc a) rest else acc
in
utest sum 0 list with 3 in
utest sum 0 rope with 3 in

-- Higher-order operations. The callbacks are curried, as MExpr requires.
utest foldl (lam acc. lam x. addi acc x) 0 [1, 2, 3] with 6 in
utest foldr (lam x. lam acc. subi x acc) 0 [1, 2, 3] with 2 in
utest foldl (lam acc. lam c. cons c acc) "" "abc" with "cba" in
utest mapi (lam i. lam x. addi i x) [10, 20, 30] with [10, 21, 32] in

-- Sequence patterns.
let classify = lam xs.
  match xs with [] then 0
  else match xs with [a] then a
  else match xs with [a, b] then addi a b
  else match xs with [a] ++ rest then addi a (length rest)
  else 99
in
utest classify [] with 0 in
utest classify [7] with 7 in
utest classify [3, 4] with 7 in
utest classify [1, 1, 1, 1] with 4 in

-- An edge pattern with a postfix.
let ends = lam xs. match xs with [a] ++ _ ++ [b] then addi a b else 0 in
utest ends [1, 9, 9, 2] with 3 in

utest string2float "2.5" with 2.5 in
utest stringIsFloat "2.5" with true in
utest stringIsFloat "abc" with false in

-- What reaches the host. A string has to leave the sequence representation on
-- the way out, and a float has to be formatted as the reference backend
-- formats it, so these are printed rather than compared here.
let nl = "\n" in
let puts = lam s. print (concat s nl) in
let putf = lam x. puts (float2string x) in
puts "hello world";
puts mixed;
iter (lam c. print [c]) "iter"; print nl;
iteri (lam i. lam c. print (concat (if eqi i 0 then "0" else "1") [c])) "ab"; print nl;
putf 1.0;
putf 0.1;
putf (divf 1.0 3.0);
putf 1e300;
putf (negf 2.5);
putf (string2float "2.5")
