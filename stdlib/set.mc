-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines a set wrapper around the map intrinsics.


include "map.mc"

type Set a = Map a {}

let setEmpty : (a -> a -> Int) -> Set a = lam cmp. mapEmpty cmp
let setSize : Set a -> Int = mapSize
let setInsert : a -> Set a -> Set a = lam e. lam s. mapInsert e {} s
let setRemove : a -> Set a -> Set a = lam e. lam s. mapRemove e s
let setMem : a -> Set a -> Bool = lam e. lam s. mapMem e s
let setUnion : Set a -> Set a -> Set a = lam s1. lam s2. mapUnion s1 s2
let setOfSeq : (a -> a -> Int) -> [a] -> Set a =
lam cmp. lam seq.
  foldr setInsert (setEmpty cmp) seq
let setToSeq : Set a -> [a] = lam s. mapKeys s

mexpr

let s = setEmpty subi in
utest setSize s with 0 in
utest setMem 1 s with false in

let s1 = setInsert 1 s in
utest setSize s1 with 1 in
utest setMem 1 s1 with true in

let s0 = setRemove 1 s in
utest setSize s0 with 0 in
utest setMem 1 s0 with false in

let s2 = setOfSeq subi [2, 3] in
utest setSize s2 with 2 in
utest setMem 2 s2 with true in
utest setMem 3 s2 with true in

let s3 = setOfSeq subi (setToSeq s2) in
utest setSize s3 with 2 in
utest setMem 2 s3 with true in
utest setMem 3 s3 with true in

let s4 = setUnion s1 s2 in
utest setSize s4 with 3 in
utest setMem 1 s4 with true in
utest setMem 2 s4 with true in
utest setMem 3 s4 with true in

()
