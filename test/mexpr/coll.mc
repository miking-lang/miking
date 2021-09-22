-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Collection intrinstics

include "option.mc"
include "common.mc"

mexpr
let append = lam c1. lam c2. fold insert c2 c1 in
let size = fold (lam. addi 1) 0 in

recursive let myFun : Int -> a -> Coll p a =
  lam n. lam x.
    if lti n 1 then
      insert x empty
    else
      let c = myFun (subi n 1) x in
      append c c
in

let mySequence : Coll {}       = myFun 3 1 in
utest size mySequence with 8 in

let mySet      : Coll {UQ, NS} = myFun 3 1 in
-- utest size mySet      with 1 in


let magicSort : [a] -> [a] = lam seq.
  let c : Coll {NS} = foldr insert empty seq in
  fold cons [] c
in

-- utest magicSort     [2,2,1] with [1,2,2] in

let magicDistinct : [a] -> [a] = lam seq.
  let c : Coll {UQ} = foldr insert empty seq in
  fold cons [] c
in

-- utest magicDistinct [2,2,1] with [2,1]   in

let uncons =
  let step = lam h. lam r.
    Some (optionMapOr (h,empty) (lam t. (h, uncurry insert t)) r)
  in
  fold step (None ())
in
let head = lam c : Coll p a. optionMap         (lam x: (a, [a]). x.0) (uncons c) in
let tail = lam c : Coll p a. optionMapOr empty (lam x: (a, [a]). x.1) (uncons c) in

type Tree a in
con Leaf : () -> Tree a in
con Node : (a, Tree a, Tree a) -> Tree a in

let bfs : (a -> a -> Bool) -> a -> Tree a -> Bool
  = lam eq. lam x. lam t.
  recursive let work = lam queue.
    let h = head queue in
    match h with None () then
      false
    else match h with Some (Leaf ()) then
      work (tail queue)
    else match h with Some (Node (v, l, r)) then
      if eq v x then
        true
      else
        work (append (tail queue) (insert l (insert r empty)))
    else never
  in
  let initialQueue : Coll {} = insert t empty in
  work initialQueue
in

let t1 = Node (1, Leaf (), Node (2, Leaf (), Leaf ())) in
utest bfs eqi 2 t1 with true in

let t2 = Node (1, Node (3, Leaf (), Leaf ()), Leaf ()) in
utest bfs eqi 2 t2 with false in

()
