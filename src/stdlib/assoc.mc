-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple library that defines map operations over sequences of tuples.

include "option.mc"
include "char.mc"
include "string.mc"

type AssocMap k v = [(k, v)]
type AssocTraits k = {eq : k -> k -> Bool}

-- 'assocEmpty' is an empty associate map
let assocEmpty : all k. all v. AssocMap k v =
  []

-- 'assocLength m' returns the number of key-value pairs in m
let assocLength : all k. all v. AssocMap k v -> Int =
  length

-- 'assocInsert traits k v m' returns a new map, where the key-value pair
-- ('k','v') is stored. If 'k' is already a key in 'm', its old value will be
-- overwritten.
let assocInsert : all k. all v. AssocTraits k -> k -> v -> AssocMap k v -> AssocMap k v =
  lam traits. lam k. lam v. lam m.
    optionMapOrElse (lam. cons (k,v) m)
                    (lam i. set m i (k,v))
                    (index (lam t : (k, v). traits.eq k t.0) m)

-- 'seq2assoc traits ls' constructs a new association map from a sequence
-- of tuples 'ls'. Bindings to the right overwrites previous equal bindings to
-- the left.
let seq2assoc : all k. all v. AssocTraits k -> [(k,v)] -> AssocMap k v =
  lam traits. lam ls.
    foldl (lam acc. lam t : (k, v). assocInsert traits t.0 t.1 acc) assocEmpty ls

-- 'assoc2seq traits m' constructs a new sequence of tuples representing the association map 'm'.
-- The order of the elements in the sequence is unspecified.
let assoc2seq : all k. all v. AssocTraits k -> AssocMap k v -> [(k,v)] =
  lam traits. lam m.
    m

-- 'assocRemove traits k m' returns a new map, where 'k' is not a key. If 'k' is
-- not a key in 'm', the map remains unchanged after the operation.
let assocRemove : all k. all v. AssocTraits k -> k -> AssocMap k v -> AssocMap k v =
  lam traits. lam k. lam m.
    optionMapOr m
                (lam i.
                  let spl : ([(k, v)], [(k, v)]) = splitAt m i in
                  concat spl.0 (tail spl.1))
                (index (lam t : (k, v). traits.eq k t.0) m)


-- 'assocLookup traits k m' looks up the key 'k' and returns an Option type.
-- If 'm' has the key 'k' stored, its value is returned, otherwise None () is
-- returned.
let assocLookup : all k. all v. AssocTraits k -> k -> AssocMap k v -> Option v =
  lam traits. lam k. lam m.
    optionMapOr (None ())
                (lam t : (k, v). Some t.1)
                (find (lam t : (k, v). traits.eq k t.0) m)

-- 'assocLookupOrElse traits d k m' returns the value of key 'k' in 'm' if it
-- exists, otherwise returns the result of 'd ()'.
let assocLookupOrElse : all k. all v.
  AssocTraits k -> (() -> v) -> k -> AssocMap k v -> v =
  lam traits. lam d. lam k. lam m.
    optionGetOrElse d
                    (assocLookup traits k m)

-- 'assocLookupPred p m' returns the associated value of a key that satisfies
-- the predicate 'p'. If several keys satisfies 'p', the one that happens to be
-- found first is returned.
let assocLookupPred : all k. all v. (k -> Bool) -> AssocMap k v -> Option v =
  lam p. lam m.
    optionMapOr (None ())
                (lam t : (k, v). Some t.1)
                (find (lam t : (k, v). p t.0) m)

-- 'assocAny p m' returns true if at least one (k,v) pair in the map satisfies
-- the predicate 'p'.
let assocAny : all k. all v. (k -> v -> Bool) -> AssocMap k v -> Bool =
  lam p. lam m.
    any (lam t : (k, v). p t.0 t.1) m

-- 'assocAll p m' returns true if all (k,v) pair in the map satisfies
-- the predicate 'p'.
let assocAll : all k. all v. (k -> v -> Bool) -> AssocMap k v -> Bool =
  lam p. lam m.
    forAll (lam t : (k, v). p t.0 t.1) m

-- 'assocMem traits k m' returns true if 'k' is a key in 'm', else false.
let assocMem : all k. all v. AssocTraits k -> k -> AssocMap k v -> Bool =
  lam traits. lam k. lam m.
    optionIsSome (assocLookup traits k m)

-- 'assocKeys traits m' returns a list of all keys stored in 'm'
let assocKeys : all k. all v. AssocTraits k -> AssocMap k v -> [k] =
  lam. lam m.
    map (lam t : (k, v). t.0) m

-- 'assocValues traits m' returns a list of all values stored in 'm'
let assocValues : all k. all v. AssocTraits k -> AssocMap k v -> [v] =
  lam. lam m.
    map (lam t : (k, v). t.1) m

-- 'assocMap traits f m' maps over the values of 'm' using function 'f'.
let assocMap : all k. all v1. all v2.
  AssocTraits k -> (v1 -> v2) -> AssocMap k v1 -> AssocMap k v2 =
  lam. lam f. lam m.
    map (lam t : (k, v1). (t.0, f t.1)) m

-- 'assocMapWithKey f m' maps over the values of 'm' using function 'f', where 'f' additionally has access to the key of the value being operated upon.
let assocMapWithKey : all k. all v1. all v2.
  AssocTraits k -> (k -> v1 -> v2) -> AssocMap k v1 -> AssocMap k v2 =
  lam. lam f. lam m.
    map (lam t : (k, v1). (t.0, f t.0 t.1)) m

-- 'assocFold traits f acc m' folds over 'm' using function 'f' and accumulator
-- 'acc'.
-- IMPORTANT: The folding order is unspecified.
let assocFold : all k. all v. all acc. AssocTraits k -> (acc -> k -> v -> acc)
                  -> acc -> AssocMap k v -> acc =
  lam. lam f. lam acc. lam m.
    foldl (lam acc. lam t : (k, v). f acc t.0 t.1) acc m

-- 'assocFoldlM traits f acc m' folds over 'm' using function 'f' and accumulator
-- 'acc'. The folding stops immediately if 'f' returns 'None ()'.
-- IMPORTANT: The folding order is unspecified.
let assocFoldlM : all k. all v. all acc. AssocTraits k -> (acc -> k -> v -> Option acc)
                        -> acc -> AssocMap k v -> Option acc =
  lam. lam f. lam acc. lam m.
    optionFoldlM (lam acc. lam t : (k, v). f acc t.0 t.1) acc m

-- 'assocMapAccum traits f acc m' simultaneously performs a map (over values)
-- and fold over 'm' using function 'f' and accumulator 'acc'.
-- IMPORTANT: The folding order is unspecified.
let assocMapAccum : all k. all v1. all v2. all acc.
  AssocTraits k -> (acc -> k -> v1 -> (acc, v2))
                -> acc -> AssocMap k v1 -> (acc, AssocMap k v2) =
  lam. lam f. lam acc. lam m.
    mapAccumL
      (lam acc. lam t : (k, v1).
         let fval : (acc, v2) = f acc t.0 t.1 in
         match fval with (acc, b) then (acc, (t.0, b)) else never)
      acc m

-- 'assocMergePreferRight traits l r' merges two maps, keeping values from r in case a key
-- exists in both maps. See also 'assocMergePreferLeft'
let assocMergePreferRight
  : all k. all v. AssocTraits k -> AssocMap k v -> AssocMap k v -> AssocMap k v =
  lam traits. lam l. lam r.
    assocFold traits (lam m. lam k. lam v. assocInsert traits k v m) l r

-- 'assocMergePreferLeft traits l r' merges two maps, keeping values from l in case a key
-- exists in both maps. See also 'assocMergePreferRight'
let assocMergePreferLeft
  : all k. all v. AssocTraits k -> AssocMap k v -> AssocMap k v -> AssocMap k v =
  lam traits. lam l. lam r. assocMergePreferRight traits r l

mexpr

let traits = {eq = eqi} in

let length = assocLength in
let lookup = lam x. assocLookup traits x in
let lookupOrElse = lam x. assocLookupOrElse traits x in
let lookupPred = assocLookupPred in
let any = assocAny in
let forAll = assocAll in
let insert = lam x. assocInsert traits x in
let seq2assoc = lam x. seq2assoc traits x in
let assoc2seq = lam x. assoc2seq traits x in
let mem = lam x. assocMem traits x in
let remove = lam x. assocRemove traits x in
let keys = lam x. assocKeys traits x in
let values = lam x. assocValues traits x in
let map = lam x. assocMap traits x in
let mapWithKey = lam x. assocMapWithKey traits x in
let fold = lam x. assocFold traits x in
let foldOption = lam x. assocFoldlM traits x in
let mapAccum = lam x. assocMapAccum traits x in
let mergePreferLeft = lam x. assocMergePreferLeft traits x in
let mergePreferRight = lam x. assocMergePreferRight traits x in

let m = assocEmpty in
let m = insert 1 '1' m in
let m = insert 2 '2' m in
let m = insert 3 '3' m in

utest length m with 3 in
utest lookup 1 m with Some '1' using optionEq eqChar in
utest lookup 2 m with Some '2' using optionEq eqChar in
utest lookup 3 m with Some '3' using optionEq eqChar in
utest lookup 4 m with None () using optionEq eqChar in
utest lookupOrElse (lam. 'x') 1 m with '1' in
utest lookupOrElse (lam. 'x') 2 m with '2' in
utest lookupOrElse (lam. 'x') 3 m with '3' in
utest lookupPred (eqi 2) m with Some '2' using optionEq eqChar in
utest any (lam k. lam v. eqChar v '2') m with true in
utest any (lam k. lam v. eqChar v '4') m with false in
utest forAll (lam k. lam v. gti k 0) m with true in
utest forAll (lam k. lam v. gti k 1) m with false in
utest
  match keys m with [1,2,3] | [1,3,2] | [2,1,3] | [2,3,1] | [3,1,2] | [3,2,1]
  then true else false
with true in
utest
  match values m with "123" | "132" | "213" | "231" | "312" | "321"
  then true else false
with true in

let seq = [(1, '1'), (2, '2'), (3, '3')] in
let m = seq2assoc seq in

utest sort (lam l : (Int, Char). lam r : (Int, Char). subi l.0 r.0) (assoc2seq m)
with [(1, '1'), (2, '2'), (3, '3')] in

let withKeyMap = mapWithKey (lam k. lam v. (k, v)) m in
let eqOptionTuple =
  optionEq (lam t1 : (Int, Char). lam t2 : (Int, Char).
              and (eqi t1.0 t2.0) (eqChar t1.1 t2.1)) in
utest lookup 1 withKeyMap with Some (1, '1') using eqOptionTuple in
utest lookup 2 withKeyMap with Some (2, '2') using eqOptionTuple in
utest lookup 3 withKeyMap with Some (3, '3') using eqOptionTuple in

let nextChar = lam c. int2char (addi 1 (char2int c)) in

let eqOptionTriple =
  lam t1 : (Option Char, Option Char, Option Char).
    lam t2 : (Option Char, Option Char, Option Char).
      and (optionEq eqc t1.0 t2.0)
        (and (optionEq eqc t1.1 t2.1) (optionEq eqc t1.2 t2.2)) in
let mapm = (map nextChar m) in
utest (lookup 1 mapm, lookup 2 mapm, lookup 3 mapm)
with (Some '2', Some '3', Some '4') using eqOptionTriple in

utest fold (lam acc. lam k. lam v. addi acc k) 0 m with 6 in
utest fold (lam acc. lam k. lam v. and acc (isDigit v)) true m with true in

utest foldOption (lam acc. lam k. lam v. Some (addi acc k)) 0 m with Some 6
using optionEq eqi in
utest foldOption (lam acc. lam k. lam v. if eqi k 4 then None () else Some acc)
        true m
with Some true using optionEq eqBool in
utest foldOption (lam acc. lam k. lam v. if eqi k 2 then None () else Some acc)
        true m
with None () using optionEq eqBool in

let mapaccm = mapAccum (lam acc. lam k. lam v. (addi acc k, nextChar v)) 0 m in
utest (mapaccm.0, (lookup 1 mapaccm.1, lookup 2 mapaccm.1, lookup 3 mapaccm.1))
with (6, (Some '2', Some '3', Some '4'))
using
  lam t1 : (Int, (Option Char, Option Char, Option Char)).
    lam t2 : (Int, (Option Char, Option Char, Option Char)).
      and (eqi t1.0 t2.0) (eqOptionTriple t1.1 t2.1) in

let m = insert 1 '2' m in
let m = insert 2 '3' m in
let m = insert 3 '4' m in
let m = insert 4 '5' m in

utest lookup 1 m with Some '2' using optionEq eqChar in
utest lookup 2 m with Some '3' using optionEq eqChar in
utest lookup 3 m with Some '4' using optionEq eqChar in
utest lookup 4 m with Some '5' using optionEq eqChar in

let m = [(1,3), (4,6)] in

let m = assocEmpty in
let m = insert 1 3 m in
let m = insert 4 6 m in
let m = insert 2 3 m in

utest mem 1 m with true in
utest mem 2 m with true in
utest mem 3 m with false in
utest mem 4 m with true in

let m = remove 2 m in

utest mem 2 m with false in
utest mem 1 m with true in
utest mem 4 m with true in

let m = remove 1 m in
let m = remove 3 m in

utest mem 1 m with false in
utest mem 4 m with true in

let m = remove 4 m in

utest mem 4 m with false in

let m1 = insert 1 "1l" (insert 2 "2l" assocEmpty) in
let m2 = insert 1 "1r" (insert 3 "3r" assocEmpty) in
let ml = mergePreferLeft m1 m2 in
let mr = mergePreferRight m1 m2 in

let eqIntOptStringTuple =
  lam t1 : (Int, String). lam t2 : (Int, String).
    and (eqi t1.0 t2.0) (eqString t1.1 t2.1)
in

utest ml with mergePreferRight m2 m1 using eqSeq eqIntOptStringTuple in
utest lookup 1 ml with Some "1l" using optionEq eqString in
utest lookup 2 ml with Some "2l" using optionEq eqString in
utest lookup 3 ml with Some "3r" using optionEq eqString in

utest mr with mergePreferLeft m2 m1 using eqSeq eqIntOptStringTuple in
utest lookup 1 mr with Some "1r" using optionEq eqString in
utest lookup 2 mr with Some "2l" using optionEq eqString in
utest lookup 3 mr with Some "3r" using optionEq eqString in

()
