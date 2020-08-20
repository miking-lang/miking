-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple library that defines map operations over sequences of tuples.

include "option.mc"
include "set.mc"

type AssocMap = [(k, v)]
type AssocTraits = {eq : k -> k -> Bool}

-- 'assocEmpty ()' returns an empty associate map
let assocEmpty : Unit -> AssocMap = lam _.
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


-- 'assocLookupOpt traits k m' looks up the key 'k' and returns an Option type.
-- If 'm' has the key 'k' stored, its value is returned, otherwise None () is
-- returned.
let assocLookupOpt : AssocTraits -> k -> AssocMap -> OptionV =
  lam traits. lam k. lam m.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. traits.eq k t.0) m)

-- 'assocLookup traits k m' returns the value of key 'k' in 'm'. Throws an error
-- if 'k' does not exist in 'm'.
let assocLookup : AssocTraits -> k -> AssocMap -> v =
  lam traits. lam k. lam m.
    optionGetOrElse (lam _. error "Element not found")
                    (assocLookupOpt traits k m)

-- 'assocMem traits k m' returns true if 'k' is a key in 'm', else false.
let assocMem : AssocTraits -> k -> AssocMap -> Bool =
  lam traits. lam k. lam m.
    optionIsSome (assocLookupOpt traits k m)

mexpr

let traits = {eq = eqi} in

let lookupOpt = assocLookupOpt traits in
let lookup = assocLookup traits in
let insert = assocInsert traits in
let mem = assocMem traits in
let remove = assocRemove traits in

let m = assocEmpty () in
let m = insert 1 '1' m in
let m = insert 2 '2' m in
let m = insert 3 '3' m in

utest lookupOpt 1 m with Some '1' in
utest lookupOpt 2 m with Some '2' in
utest lookupOpt 3 m with Some '3' in
utest lookupOpt 4 m with None () in

let m = insert 1 '2' m in
let m = insert 2 '3' m in
let m = insert 3 '4' m in
let m = insert 4 '5' m in

utest lookupOpt 1 m with Some '2' in
utest lookupOpt 2 m with Some '3' in
utest lookupOpt 3 m with Some '4' in
utest lookupOpt 4 m with Some '5' in

let m = [(1,3), (4,6)] in

let m = assocEmpty () in
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
