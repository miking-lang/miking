// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test integer primitives

mexpr

// Construction of lists
utest [] with [] in
utest [1,2] with [1,2] in
utest [[2,3,10],7] with [[2,3,10],7] in

// makeseq n v
utest makeseq 3 10 with [10,10,10] in
utest makeseq 8 'a' with ['a','a','a','a','a','a','a','a'] in
utest makeseq 0 100 with [] in

// concat l1 l2
utest concat [1,2,3] [10] with [1,2,3,10] in
utest concat [1] [3] with [1,3] in
utest concat [] [3,10] with [3,10] in
utest concat ['a','b'] [] with ['a','b'] in

// nth lst n
utest nth [1,3,9] 2 with 9 in
utest nth [5] 0 with 5 in
utest nth [5,addi 2 3] 1 with 5 in

// cons x xs
utest cons 1 [8,10] with [1,8,10] in
utest cons 'a' [] with ['a'] in

// slice lst start length
utest slice [1,3,5] 0 2 with [1,3] in
utest slice [3,7,10,20] 1 3 with [7,10,20] in
utest slice ['a','b'] 1 10 with ['b'] in
utest slice [1,3] 2 10 with [] in

// reverse lst
utest reverse [1,7,10] with [10,7,1] in
utest reverse ['a'] with ['a'] in
utest reverse [] with [] in

// head and tail
let head = lam seq. nth seq 0 in
let tail = lam seq. slice seq 1 (length seq) in
utest head [2,3,5] with 2 in
utest tail [2,4,8] with [4,8] in

// map
let map = fix (lam map. lam f. lam seq.
  if eqi (length seq) 0 then []
  else cons (f (head seq)) (map f (tail seq))
) in
utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21] in
utest map (lam x. addi x 1) [] with [] in

// foldl
let foldl = fix (lam foldl. lam f. lam acc. lam seq.
    if eqi (length seq) 0 then acc
    else foldl f (f acc (head seq)) (tail seq)
) in
utest foldl addi 0 [1,2,3,4,5] with 15 in
utest foldl addi 0 [] with 0 in
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16] in

// zipwith
let zipwith = fix (lam zipwith. lam f. lam seq1. lam seq2.
    if eqi (length seq1) 0 then []
    else if eqi (length seq2) 0 then []
    else cons (f (head seq1) (head seq2)) (zipwith f (tail seq1) (tail seq2))
) in
utest zipwith addi [1,2,3,4,5] [5, 4, 3, 2, 1] with [6,6,6,6,6] in
utest zipwith (zipwith addi) [[1,2], [], [10, 10, 10]] [[3,4,5], [1,2], [2, 3]]
      with [[4,6], [], [12, 13]] in
utest zipwith addi [] [] with [] in

()
