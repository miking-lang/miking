-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines a set wrapper around the map intrinsics.


include "map.mc"

type Set a = Map a {}

-- `setEmpty cmp` creates an empty set ordered by `cmp`.
let setEmpty : all a. (a -> a -> Int) -> Set a = lam cmp. mapEmpty cmp

-- The size of a set.
let setSize : all a. Set a -> Int = mapSize

-- Is the set empty?
let setIsEmpty : all a. Set a -> Bool = mapIsEmpty

-- `setInsert e s` inserts element `e` into set `s`.
let setInsert : all a. a -> Set a -> Set a = lam e. lam s. mapInsert e {} s

-- `setRemove e s` removes element `e` from set `s`.
let setRemove : all a. a -> Set a -> Set a = lam e. lam s. mapRemove e s

-- Is the element member of the set?
let setMem : all a. a -> Set a -> Bool = lam e. lam s. mapMem e s

-- Is s1 a subset of s2?
let setSubset : all a. Set a -> Set a -> Bool = lam s1. lam s2.
  mapAllWithKey (lam e. lam. mapMem e s2) s1

-- `setUnion s1 s2` is the union of set `s1` and `s2`.
let setUnion : all a. Set a -> Set a -> Set a = lam s1. lam s2. mapUnion s1 s2

-- `setIntersect s1 s2` is the intersection of set `s1` and `s2`.
let setIntersect : all a. Set a -> Set a -> Set a = lam s1. lam s2.
  let cmp = mapGetCmpFun s1 in
  mapFoldWithKey (lam acc. lam key. lam.
    if setMem key s2 then setInsert key acc else acc
  ) (setEmpty cmp) s1

-- `setSubtract s1 s2` is the relative complement of set `s2` in `s1` (set
-- difference, i.e., s1 - s2).
let setSubtract : all a. Set a -> Set a -> Set a = lam s1. lam s2.
  let cmp = mapGetCmpFun s1 in
  mapFoldWithKey (lam acc. lam key. lam. mapRemove key acc) s1 s2


-- `setOfSeq cmp seq` construct a set ordered by `cmp` from a sequence `seq`.
let setOfSeq : all a. (a -> a -> Int) -> [a] -> Set a =
lam cmp. lam seq.
  foldr setInsert (setEmpty cmp) seq

-- `setFold f acc s` folds over the values of s with the given function and
-- initial accumulator
let setFold : all a. all acc. (acc -> a -> acc) -> acc -> Set a -> acc =
  lam f. lam acc. lam s.
    mapFoldWithKey (lam acc. lam k. lam. f acc k) acc s

-- Transform a set to a sequence.
let setToSeq : all a. Set a -> [a] = lam s. mapKeys s

-- Two sets are equal, where equality is determined by the compare function.
-- Both sets are assumed to have the same equality function.
let setEq : all a. Set a -> Set a -> Bool = mapEq (lam. lam. true)

-- `setCmp` provides comparison over sets.
let setCmp : all a. Set a -> Set a -> Int = mapCmp (lam. lam. 0)

-- `setChoose s` chooses one element from the set `s`, giving `None ()` if `s`
-- is empty.
let setChoose : all a. Set a -> Option a =
  lam s. match mapChoose s with Some (k, _) then Some k else None ()

-- `setChooseExn s` chooses one element from the set `s`, giving `error` if `s`
-- is empty.
let setChooseExn : all a. Set a -> a =
lam s.
  match mapChooseExn s with (k, _) then k else never

-- `setAny p s` returns true if the predicate p returns true for any element in
-- s.
let setAny: all a. (a -> Bool) -> Set a -> Bool = lam p. lam s.
  mapFoldWithKey (lam acc. lam v. lam. if acc then acc else p v) false s

mexpr

let s = setEmpty subi in
utest setSize s with 0 in
utest setMem 1 s with false in
utest setChoose s with None () in
utest setIsEmpty s with true in

let s1 = setInsert 1 s in
utest setSize s1 with 1 in
utest setMem 1 s1 with true in
utest setChooseExn s1 with 1 in
utest setChoose s1 with Some 1 in
utest setIsEmpty s1 with false in

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

utest setEq s4 s4 with true in
utest setEq s4 s3 with false in

let s5 = setOfSeq subi [1,2,3,4,5] in
let s6 = setOfSeq subi [1,2,3] in
let s7 = setOfSeq subi [1,2,6] in
utest setSubset s5 s5 with true in
utest setSubset s6 s5 with true in
utest setSubset s7 s5 with false in

let sInt1 = setIntersect (setOfSeq subi []) (setOfSeq subi [1]) in
utest setSize sInt1 with 0 in

let sInt2 = setIntersect (setOfSeq subi [1,2]) (setOfSeq subi [2]) in
utest setSize sInt2 with 1 in
utest setMem 2 sInt2 with true in

utest setSubtract s5 (setEmpty subi) with s5 using setEq in
utest setSubtract s5 s6 with setOfSeq subi [4,5] using setEq in

utest setCmp s5 s5 with 0 in
utest setCmp s5 s6 with 1 in
utest setCmp s6 s5 with negi 1 in
utest setCmp s5 s7 with negi 3 in
utest setCmp s7 s5 with 3 in
utest setCmp s6 s7 with negi 3 in

utest setAny (eqi 2) s5 with true in
utest setAny (eqi 0) s5 with false in

let sFold = setOfSeq subi [1,2,3,4,5] in
utest setFold (lam acc. lam v. addi v acc) 0 sFold with 15 in

()
