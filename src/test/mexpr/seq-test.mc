-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test integer primitives

include "common.mc"

-- Helper function for tests
let eqSeq : all a. (a -> a -> Bool) -> [a] -> [a] -> Bool =
  lam eq : (a -> a -> Bool).
  recursive let work = lam as. lam bs.
    let pair = (as, bs) in
    match pair with ([], []) then true else
    match pair with ([a] ++ as, [b] ++ bs) then
      if eq a b then work as bs else false
      else false
    in work

utest eqSeq eqi [] [] with true
utest eqSeq eqi [1] [] with false
utest eqSeq eqi [] [1] with false
utest eqSeq eqi [1] [1] with true
utest eqSeq eqi [1] [2] with false
utest eqSeq eqi [2] [1] with false

mexpr

-- Construction of lists
utest [] with [] using eqSeq eqi in
utest [1,2] with [1,2] in
--utest [[2,3,10],7] with [[2,3,10],7] in

-- 'create n f' creates a new sequence with 'n' elements of value given
-- by calling function 'f' with the index of the element
-- Int -> (Int -> a) -> [a]
utest create 3 (lam. 10) with [10,10,10] in
utest create 8 (lam. 'a') with ['a','a','a','a','a','a','a','a'] in
utest create 4 (lam i. muli 2 i) with [0,2,4,6] in
utest create 0 (lam i. i) with [] using eqSeq eqi in

-- 'createList n f' is like 'create n f', but the underlying representation of
-- the sequence is a const list.
-- Int -> (Int -> a) -> [a]
utest
  let s = createList 3 (lam i. i) in
  [get s 0, get s 1, get s 2]
with [0, 1, 2] in

-- 'createRope n f' is like 'create n f', but the underlying representation of
-- the sequence is a rope.
-- Int -> (Int -> a) -> [a]
utest
  let s = createRope 3 (lam i. i) in
  [get s 0, get s 1, get s 2]
with [0, 1, 2] in

-- 'isList s' and 'isRope s' check if the sequence is a list or a rope,
-- respectively.
utest isList (createList 3 (lam i. i)) with true in
utest isList (createRope 3 (lam i. i)) with false in
utest isRope (createRope 3 (lam i. i)) with true in
utest isRope (createList 3 (lam i. i)) with false in

-- 'length s' returns the length of a sequence (or a string)
utest length [] with 0 in
utest length [4,5,1,7,9] with 5 in
utest length "hi" with 2 in

-- 'concat s1 s2' returns the concatenation of 's1' and 's2'
-- [a] -> [a] -> [a]
utest concat [1,2,3] [10] with [1,2,3,10] in
utest concat [1] [3] with [1,3] in
utest concat [] [3,10] with [3,10] in
utest concat ['a','b'] [] with ['a','b'] in

-- concat preserves the representation if the inputs agree, otherwise
-- the result is a list
utest isRope (concat (createRope 3 (lam i. i)) (createRope 3 (lam i. i))) with true in
utest isRope (concat (createList 3 (lam i. i)) (createRope 3 (lam i. i))) with false in
utest isList (concat (createList 3 (lam i. i)) (createRope 3 (lam i. i))) with true in
utest isList (concat (createRope 3 (lam i. i)) (createList 3 (lam i. i))) with true in
utest isList (concat (createList 3 (lam i. i)) (createList 3 (lam i. i))) with true in

-- Lists and ropes are otherwise indistinguishable
utest createList 3 (lam i. i) with [0, 1, 2] in
utest createList 3 (lam i. i) with [0, 1, 2] using eqSeq eqi in

-- 'get s n' returns element with index 'n' from sequence 's'
-- [a] -> Int -> a
utest get [1,3,9] 2 with 9 in
utest get [5] 0 with 5 in
utest get [5,addi 2 3] 1 with 5 in

-- 'set s n v' returns a sequence based on sequence 's', where
-- an element with index 'n' is replaced with value 'v'
utest set [1,2,3] 0 4 with [4,2,3] in
utest set [1] 0 2 with [2] in
utest set [1,2,3] 2 (addi 1 3) with [1,2,4] in

-- 'cons x xs' returns a new sequence by performing the cons
-- operation by prepending element 'x' to a sequence 'xs'.
utest cons 1 [8,10] with [1,8,10] in
utest cons 'a' [] with ['a'] in

-- 'snoc xs x' returns a sequence where element 'x' is appended
-- to then end of a sequence 'xs'
utest snoc [1,2] 3 with [1,2,3] in
utest snoc [] 1 with [1] in

-- 'splitAt s n' returns a tuple containing two sequences, where
-- sequence 's' is split into two sequence at index 'n'.
let seqTupleEq = lam t1 : ([Int], [Int]). lam t2 : ([Int], [Int]).
  and (eqSeq eqi t1.0 t2.0) (eqSeq eqi t1.1 t2.1)
in

utest splitAt [1,2,3] 0 with ([],[1,2,3]) using seqTupleEq in
utest splitAt [1,2,3] 1 with ([1],[2,3]) in
utest splitAt [1,2,3] 2 with ([1,2],[3]) in
utest splitAt [1,2,3] 3 with ([1,2,3],[]) using seqTupleEq in

-- 'reverse s' returns a new string where sequence 's' is reversed.
utest reverse [1,7,10] with [10,7,1] in
utest reverse ['a'] with ['a'] in
utest reverse [] with [] using eqSeq eqi in

-- 'subsequence s start len' returns the subsequence of 's' of length at most
-- 'len' that starts at index 'start'
utest subsequence [1,2,3] 0 2 with [1,2] in
utest subsequence [1,2,3] 0 10 with [1,2,3] in
utest subsequence [1,2] 1 1 with [2] in

-- 'head s' returns the first element in 's'
-- [a] -> a
utest head [2,3,5] with 2 in

-- 'tail s' returns a sequence with all except the first element in 's'
-- [a] -> [a]
utest tail [2,4,8] with [4,8] in

-- 'map f s' applies 'f' to all elements in 's' and returns the resulting
-- sequence
-- (a -> b) -> [a] -> [b]
utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21] in
utest map (lam x. addi x 1) [] with [] using eqSeq eqi in

-- 'mapi f s' is similar to 'map', but 'f' takes the index of the element as its
-- first argument, and the element as its second argument
-- (Int -> a -> b) -> [a] -> [b]
utest mapi (lam i. lam x. i) [3,4,8,9,20] with [0,1,2,3,4] in
utest mapi (lam i. lam x. i) [] with [] using eqSeq eqi in

-- 'iter f s' applies 'f' to every element in 's'
-- (a -> ()) -> [a] -> ()
utest iter (lam x. addi x 1; ()) [1, 2, 3]
with () in

utest
  let r = ref 0 in
  iter (lam x. modref r (addi x (deref r))) [1, 2, 3, 4];
  deref r
with 10 in

utest
  let r = ref 0 in
  let s = splitAt [11, 11, 11, 11, 1, 2, 3, 4] 4 in
  iter (lam x. modref r (addi x (deref r))) s.1;
  deref r
with 10 in

-- 'iteri f s' is like 'iter' but 'f' takes the index of the element as its
-- first argument and the element as its second argument.
-- (Int -> a -> ()) -> [a] -> ()
utest iteri (lam i. lam x. addi x i; ()) [1, 2, 3]
with () in

utest
  let r = ref 0 in
  iteri (lam i. lam x. modref r (addi i (addi x (deref r)))) [1, 2, 3, 4];
  deref r
with 16 in

utest
  let r = ref 0 in
  let s = splitAt [17, 17, 17, 17, 1, 2, 3, 4] 4 in
  iteri (lam i. lam x. modref r (addi i (addi x (deref r)))) s.1;
  deref r
with 16 in

utest
 let r = ref [] in
 let x = concat (concat (concat [] [0]) [1]) [2] in
 iteri (lam i. lam x. modref r (snoc (deref r) (i, x))) x;
 deref r
with [(0, 0), (1, 1), (2, 2)] in

-- The rest of the file contains various test computions with sequences

-- map
let map = lam l. fix (lam map. lam f. lam seq.
  if eqi (length seq) 0 then []
  else cons (f (head seq)) (map f (tail seq))
) l in
utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21] in
utest map (lam x. addi x 1) [] with [] using eqSeq eqi in

-- foldl
let foldl = lam l. fix (lam foldl. lam f. lam acc. lam seq.
    if eqi (length seq) 0 then acc
    else foldl f (f acc (head seq)) (tail seq)
) l in
utest foldl addi 0 [1,2,3,4,5] with 15 in
utest foldl addi 0 [] with 0 in
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16] in

-- zipwith
let zipwith = lam l. fix (lam zipwith. lam f. lam seq1. lam seq2.
    if eqi (length seq1) 0 then []
    else if eqi (length seq2) 0 then []
    else cons (f (head seq1) (head seq2)) (zipwith f (tail seq1) (tail seq2))
) l in
utest zipwith addi [1,2,3,4,5] [5, 4, 3, 2, 1] with [6,6,6,6,6] in
utest zipwith (zipwith addi) [[1,2], [], [10, 10, 10]] [[3,4,5], [1,2], [2, 3]]
      with [[4,6], [], [12, 13]] in
utest zipwith addi [] [] with [] using eqSeq eqi in

()
