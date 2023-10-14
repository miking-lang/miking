-- Miking is licensed under the MIT license.
-- Copyright (C) Miking contributors. See file LICENSE.txt
--
-- This library defines the These type and its constructors: This, That, and
-- These.
--
-- For a `These a b` type, we refer to the values of type `a` as here-values and
-- the values of type `b` as there-values.

include "option.mc"
include "seq.mc"
include "tuple.mc"
include "basic-types.mc"

-- Construct These types
let theseThis : all a. all b. a -> These a b = lam a. This a
let theseThat : all a. all b. b -> These a b = lam b. That b
let theseThese : all a. all b. (a, b) -> These a b = lam ab. These ab

-- `t1` equal to `t2`, given equality functions `eqh` and `eqt` that compares
-- here and there-values, respectively.
let theseEq : all a. all b. all c. all d.
  (a -> c -> Bool) -> (b -> d -> Bool) -> These a b -> These c d -> Bool
  = lam eqh. lam eqt. lam t1. lam t2.
    switch (t1, t2)
    case (This a, This c) then eqh a c
    case (That b, That d) then eqt b d
    case (These (a, b), These (c, d)) then and (eqh a c) (eqt b d)
    case _ then false
    end

utest
  let theseEq = theseEq eqi eqi in
  utest theseEq (This 0) (This 0) with true in
  utest theseEq (This 0) (This 1) with false in
  utest theseEq (This 0) (That 0) with false in
  utest theseEq (This 0) (These (0, 0)) with false in
  utest theseEq (That 0) (That 0) with true in
  utest theseEq (That 0) (That 1) with false in
  utest theseEq (That 0) (This 0) with false in
  utest theseEq (That 0) (These (0, 0)) with false in
  utest theseEq (These (0, 0)) (These (0, 0)) with true in
  utest theseEq (These (0, 0)) (These (1, 0)) with false in
  utest theseEq (These (0, 0)) (These (0, 1)) with false in
  utest theseEq (These (0, 0)) (This 0) with false in
  ()
with ()


-- Case analysis for the `These` type to extract its value.
let theseThese : all a. all b. all c. (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c
  = lam hf. lam tf. lam htf. lam t.
    switch t
    case This a then hf a
    case That b then tf b
    case These (a, b) then htf a b
    end

utest
  let theseThese =
    let hf = eqi 1 in
    let tf = eqf 0.5 in
    theseThese hf tf (lam a. lam b. and (hf a) (tf b))
  in
  utest theseThese (This 1) with true in
  utest theseThese (That 0.5) with true in
  utest theseThese (These (1, 0.5)) with true in
  utest theseThese (This 2) with false in
  utest theseThese (That 1.) with false in
  utest theseThese (These (2, 0.5)) with false in
  utest theseThese (These (1, 1.)) with false in
  ()
with ()


-- Maps a These type to a These type, where `hf` and `tf` map here and
-- there-values, respectively.
let theseBiMap : all a. all b. all c. all d. (a -> c) -> (b -> d) -> These a b -> These c d
  = lam hf. lam tf. lam t.
    switch t
    case This a then This (hf a)
    case That b then That (tf b)
    case These (a, b) then These (hf a, tf b)
    end

utest
  let theseBiMap = theseBiMap (addi 1) (lam x. subi x 1) in
  utest theseBiMap (This 1) with This 2 in
  utest theseBiMap (That 1) with That 0 in
  utest theseBiMap (These (1, 1)) with These (2, 0) in
  ()
with ()


-- Maps here-values.
let theseMapHere : all a. all b. all c. (a -> c) -> These a b -> These c b
  = lam f. lam t.
    switch t
    case This a then This (f a)
    case That b then That b
    case These (a, b) then These (f a, b)
    end

utest
  let theseMapHere = theseMapHere (addi 1) in
  utest theseMapHere (This 0) with This 1 in
  utest theseMapHere (That 0) with That 0 in
  utest theseMapHere (These (0, 0)) with These (1, 0) in
  ()
with ()


-- Maps there-values.
let theseMapThere : all a. all b. all c. (b -> c) -> These a b -> These a c
  = lam f. lam t.
    switch t
    case This a then This a
    case That b then That (f b)
    case These (a, b) then These (a, f b)
    end

utest
  let theseMapThere = theseMapThere (addi 1) in
  utest theseMapThere (This 0) with This 0 in
  utest theseMapThere (That 0) with That 1 in
  utest theseMapThere (These (0, 0)) with These (0, 1) in
  ()
with ()


-- Maps `This` to `This`, where `f` defines the mapping of its values. For the
-- other cases this is an identity map.
let theseMapThis : all a. all b. (a -> a) -> These a b -> These a b
  = lam f. lam t.
    match t with This a then This (f a) else t

utest
  let theseMapThis = theseMapThis (addi 1) in
  utest theseMapThis (This 0) with This 1 in
  utest theseMapThis (That 0) with That 0 in
  utest theseMapThis (These (0, 0)) with These (0, 0) in
  ()
with ()


-- Maps `That` to `That`, where `f` defines the mapping of its values. For the
-- other cases this is an identity map.
let theseMapThat : all a. all b. (b -> b) -> These a b -> These a b
  = lam f. lam t.
    match t with That b then That (f b) else t

utest
  let theseMapThat = theseMapThat (addi 1) in
  utest theseMapThat (This 0) with This 0 in
  utest theseMapThat (That 0) with That 1 in
  utest theseMapThat (These (0, 0)) with These (0, 0) in
  ()
with ()


-- Maps `These` to `These`, where `f` defines the mapping of its values. For the
-- other cases this is an identity map.
let theseMapThese : all a. all b. ((a, b) -> (a, b)) -> These a b -> These a b
  = lam f. lam t.
    match t with These t then These (f t) else t

utest
  let theseMapThese = theseMapThese (lam x. (addi 1 x.0, subi x.1 1)) in
  utest theseMapThese (This 0) with This 0 in
  utest theseMapThese (That 0) with That 0 in
  utest theseMapThese (These (0, 1)) with These (1, 0) in
  ()
with ()


-- Partitions a sequence of These values to a tuple of sequences: `(as, bs,
-- abs)`, where `as` are values from `This`, `bs` are values from `That`, and
-- `abs` are values from `These`.
let thesePartition : all a. all b. [These a b] -> ([a], [b], [(a, b)])
  = lam ts.
    foldl
      (lam acc. lam t.
        switch t
        case This a then (snoc acc.0 a, acc.1, acc.2)
        case That b then (acc.0, snoc acc.1 b, acc.2)
        case These ab then (acc.0, acc.1, snoc acc.2 ab)
        end)
      ([], [], [])
      ts


utest thesePartition []
  with (let t : ([Int], [String], [(Int, String)]) = ([], [], []) in t)

utest thesePartition [This 1, That "1", That "2", These (1, "1"), This 2]
  with ([1, 2], ["1", "2"], [(1, "1")])



-- Partitions a sequence of These values to a pair of sequences: `(as, bs)`,
-- where `as` are here-values and `bs` are there-values.
let thesePartitionHereThere : all a. all b. [These a b] -> ([a], [b])
  = lam ts.
    foldl
      (lam acc. lam t.
        switch t
        case This a then (snoc acc.0 a, acc.1)
        case That b then (acc.0, snoc acc.1 b)
        case These (a, b) then (snoc acc.0 a, snoc acc.1 b)
        end)
      ([], [])
      ts


utest thesePartitionHereThere []
  with (let t : ([Int], [String]) = ([], []) in t)

utest
  thesePartitionHereThere [This 1, That "1", That "2", These (2, "3"), This 3]
  with ([1, 2, 3], ["1", "2", "3"])


-- Extracts the `This` values from a list of These.
let theseCatThis : all a. all b. [These a b] -> [a]
  = lam ts.
    foldl (lam acc. lam t. match t with This a then snoc acc a else acc) [] ts

utest theseCatThis [] with (let xs : [Int] = [] in xs)
utest theseCatThis [This 1, That 3, These (0, 4), This 2] with [1, 2]


-- Extracts the `That` values from a list of These.
let theseCatThat : all a. all b. [These a b] -> [b]
  = lam ts.
    foldl (lam acc. lam t. match t with That b then snoc acc b else acc) [] ts

utest theseCatThat [] with (let xs : [Int] = [] in xs)
utest theseCatThat [This 3, That 1, These (0, 4), That 2] with [1, 2]


-- Extracts the `These` values from a list of These.
let theseCatThese : all a. all b. [These a b] -> [(a, b)]
  = lam ts.
    foldl (lam acc. lam t. match t with These ab then snoc acc ab else acc) [] ts

utest theseCatThese [] with (let xs : [(Int, Int)] = [] in xs)
utest theseCatThese [This 3, That 6, These (0, 4), That 2, These (1, 5)]
  with [(0, 4), (1, 5)]


-- Extracts the here-values from a list of These.
let theseCatHere : all a. all b. [These a b] -> [a]
  = lam ts.
    foldl
      (lam acc. lam t.
        switch t
        case This a | These (a, _) then snoc acc a
        case That _ then acc
        end)
      []
      ts

utest theseCatHere [] with (let xs : [Int] = [] in xs)
utest theseCatHere [These (0, 4), This 1, That 3, This 2] with [0, 1, 2]


-- Extracts the There-values from a list of These.
let theseCatThere : all a. all b. [These a b] -> [b]
  = lam ts.
    foldl
      (lam acc. lam t.
        switch t
        case That b | These (_, b) then snoc acc b
        case This _ then acc
        end)
      []
      ts

utest theseCatThere [] with (let xs : [Int] = [] in xs)
utest theseCatThere [These (0, 4), This 1, That 3, That 2] with [4, 3, 2]


-- Returns true iff `t` is `This`.
let theseIsThis : all a. all b. These a b -> Bool
  = lam t. match t with This _ then true else false

utest theseIsThis (This 0) with true
utest theseIsThis (That 0) with false
utest theseIsThis (These (0, 0)) with false


-- Returns true iff `t` is `That`.
let theseIsThat : all a. all b. These a b -> Bool
  = lam t. match t with That _ then true else false

utest theseIsThat (This 0) with false
utest theseIsThat (That 0) with true
utest theseIsThat (These (0, 0)) with false


-- Returns true iff `t` is `These`.
let theseIsThese : all a. all b. These a b -> Bool
  = lam t. match t with These _ then true else false

utest theseIsThese (This 0) with false
utest theseIsThese (That 0) with false
utest theseIsThese (These (0, 0)) with true


-- Returns true iff `t` has a here-value.
let theseHasHere : all a. all b. These a b -> Bool
  = lam t. match t with This _ | These _ then true else false

utest theseHasHere (This 0) with true
utest theseHasHere (That 0) with false
utest theseHasHere (These (1, 1)) with true


-- Returns true iff `t` has a there-value.
let theseHasHere : all a. all b. These a b -> Bool
  = lam t. match t with That _ | These _ then true else false

utest theseHasHere (This 0) with false
utest theseHasHere (That 0) with true
utest theseHasHere (These (1, 1)) with true

-- Extract the `This` case value as an Option.
let theseGetThis : all a. all b. These a b -> Option a
  = lam t. match t with This a then Some a else None ()

utest
  let none : Option Int = None () in
  utest theseGetThis (This 0) with Some 0 in
  utest theseGetThis (That 0) with none in
  utest theseGetThis (These (0, 1)) with none in
  ()
with ()

-- Extract the `That` case value as an Option.
let theseGetThat : all a. all b. These a b -> Option b
  = lam t. match t with That b then Some b else None ()

utest
  let none : Option Int = None () in
  utest theseGetThat (This 0) with none in
  utest theseGetThat (That 0) with Some 0 in
  utest theseGetThat (These (0, 1)) with none in
  ()
with ()


-- Extract the `These` case value as an Option.
let theseGetThese : all a. all b. These a b -> Option (a, b)
  = lam t. match t with These ab then Some ab else None ()

utest
  let none : Option (Int, Int) = None () in
  utest theseGetThese (This 0) with none in
  utest theseGetThese (That 0) with none in
  utest theseGetThese (These (0, 1)) with Some (0, 1) in
  ()
with ()


-- Extract the here-value as an Option.
let theseGetHere : all a. all b. These a b -> Option a
  = lam t. match t with This a | These (a, _) then Some a else None ()

utest
  let none : Option Int = None () in
  utest theseGetHere (This 0) with Some 0 in
  utest theseGetHere (That 0) with none in
  utest theseGetHere (These (0, 1)) with Some 0 in
  ()
with ()


-- Extract the there-value as an Option.
let theseGetThere : all a. all b. These a b -> Option b
  = lam t. match t with That b | These (_, b) then Some b else None ()

utest
  let none : Option Int = None () in
  utest theseGetThere (This 0) with none in
  utest theseGetThere (That 0) with Some 0 in
  utest theseGetThere (These (0, 1)) with Some 1 in
  ()
with ()


-- Applies `bf` to the value of the `This` case `t` or returns `t` unchanged.
let theseBindThis : all a. all b. These a b -> (a -> These a b) -> These a b
  = lam t. lam bf.
    match t with This a then bf a else t

utest
  let f : Int -> These Int Char = lam n. This (addi n 1) in
  utest theseBindThis (This 0) f with This 1 in
  utest theseBindThis (That '0') f with That '0' in
  utest theseBindThis (These (0, '0')) f with These (0, '0') in
  ()
with ()


-- Applies `bf` to the value of the `That` case `t` or returns `t` unchanged.
let theseBindThat : all a. all b. These a b -> (b -> These a b) -> These a b
  = lam t. lam bf.
    match t with That b then bf b else t

utest
  let f : Char -> These Int Char = lam. That '1' in
  utest theseBindThat (This 0) f with This 0 in
  utest theseBindThat (That '0') f with That '1' in
  utest theseBindThat (These (0, '0')) f with These (0, '0') in
  ()
with ()


-- Applies `bf` to the value of the `These` case `t` or returns `t` unchanged.
let theseBindThese : all a. all b. These a b -> ((a, b) -> These a b) -> These a b
  = lam t. lam bf.
    match t with These ab then bf ab else t

utest
  let f : (Int, Char) -> These Int Char = lam x. These (addi x.0 1, '1') in
  utest theseBindThese (This 0) f with This 0 in
  utest theseBindThese (That '0') f with That '0' in
  utest theseBindThese (These (0, '0')) f with These (1, '1') in
  ()
with ()


-- Applies `bf` to the here-value of t` or returns `t` unchanged.
let theseBindHere : all a. all b. all c. These a b -> (a -> These c b) -> These c b
  = lam t. lam bf.
    switch t
    case This a | These (a, _) then bf a
    case That b then That b
    end

utest
  let f : Int -> These Int Char = lam n. These (addi n 1, '1') in
  utest theseBindHere (This 0) f with These (1, '1') in
  utest theseBindHere (That '0') f with That '0' in
  utest theseBindHere (These (0, '0')) f with These (1, '1') in
  ()
with ()


-- Applies `bf` the to there-value of t` or returns `t` unchanged.
let theseBindThere : all a. all b. all c. These a b -> (b -> These a c) -> These a c
  = lam t. lam bf.
    switch t
    case That b | These (_, b) then bf b
    case This a then This a
    end

utest
  let f : Char -> These Int Char = lam c. These (1, c) in
  utest theseBindThere (This 0) f with This 0 in
  utest theseBindThere (That '0') f with These (1, '0') in
  utest theseBindThere (These (0, '0')) f with These (1, '0') in
  ()
with ()
