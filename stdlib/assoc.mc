-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple library that defines map operations over sequences of tuples.

include "option.mc"
include "set.mc"

type AssocMap = [(k, v)]
type AssocTraits = {eq : k -> k -> Bool}

-- 'assocEmpty' is an empty associate map
let assocEmpty : AssocMap =
   []

-- 'assocInsert traits k v m' returns a new map, where the key-value pair
-- ('k','v') is stored. If 'k' is already a key in 'm', its old value will be
-- overwritten.
let assocInsert : AssocTraits -> k -> v -> AssocMap -> AssocMap =
  lam traits. lam k. lam v. lam m.
    optionMapOrElse (lam _. cons (k,v) m)
                    (lam i. set m i (k,v))
                    (index (lam t. traits.eq k t.0) m)

-- 'assocRemove traits k m' returns a new map, where 'k' is not a key. If 'k' is
-- not a key in 'm', the map remains unchanged after the operation.
let assocRemove : AssocTraits -> k -> AssocMap -> AssocMap =
  lam traits. lam k. lam m.
    optionMapOr m
                (lam i.
                  let spl = splitAt m i in
                  concat spl.0 (tail spl.1))
                (index (lam t. traits.eq k t.0) m)


-- 'assocLookup traits k m' looks up the key 'k' and returns an Option type.
-- If 'm' has the key 'k' stored, its value is returned, otherwise None () is
-- returned.
let assocLookup : AssocTraits -> k -> AssocMap -> OptionV =
  lam traits. lam k. lam m.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. traits.eq k t.0) m)

-- 'assocLookupOrElse traits d k m' returns the value of key 'k' in 'm' if it
-- exists, otherwise returns the result of 'd ()'.
let assocLookupOrElse : AssocTraits -> (Unit -> a) -> k -> AssocMap -> vOra =
  lam traits. lam d. lam k. lam m.
    optionGetOrElse d
                    (assocLookup traits k m)

-- 'assocLookupPred p m' returns the associated value of a key that satisfies
-- the predicate 'p'. If several keys satisfies 'p', the one that happens to be
-- found first is returned.
let assocLookupPred : AssocTraits -> (k -> Bool) -> AssocMap -> OptionV =
  lam p. lam m.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. p t.0) m)

-- 'assocMem traits k m' returns true if 'k' is a key in 'm', else false.
let assocMem : AssocTraits -> k -> AssocMap -> Bool =
  lam traits. lam k. lam m.
    optionIsSome (assocLookup traits k m)

-- 'assocKeys traits m' returns a list of all keys stored in 'm'
let assocKeys : AssocTraits -> AssocMap -> [k] =
  lam _. lam m.
    map (lam t. t.0) m

-- 'assocValues traits m' returns a list of all values stored in 'm'
let assocValues : AssocTraits -> AssocMap -> [v] =
  lam _. lam m.
    map (lam t. t.1) m


mexpr

let traits = {eq = eqi} in

let lookup = assocLookup traits in
let lookupOrElse = assocLookupOrElse traits in
let lookupPred = assocLookupPred in
let insert = assocInsert traits in
let mem = assocMem traits in
let remove = assocRemove traits in
let keys = assocKeys traits in
let values = assocValues traits in

let m = assocEmpty in
let m = insert 1 '1' m in
let m = insert 2 '2' m in
let m = insert 3 '3' m in

utest lookup 1 m with Some '1' in
utest lookup 2 m with Some '2' in
utest lookup 3 m with Some '3' in
utest lookup 4 m with None () in
utest lookupOrElse (lam _. 42) 1 m with '1' in
utest lookupOrElse (lam _. 42) 2 m with '2' in
utest lookupOrElse (lam _. 42) 3 m with '3' in
utest lookupPred (eqi 2) m with Some '2' in
utest
  match keys m with [1,2,3] | [1,3,2] | [2,1,3] | [2,3,1] | [3,1,2] | [3,2,1]
  then true else false
with true in
utest
  match values m with "123" | "132" | "213" | "231" | "312" | "321"
  then true else false
with true in

let m = insert 1 '2' m in
let m = insert 2 '3' m in
let m = insert 3 '4' m in
let m = insert 4 '5' m in

utest lookup 1 m with Some '2' in
utest lookup 2 m with Some '3' in
utest lookup 3 m with Some '4' in
utest lookup 4 m with Some '5' in

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

()
