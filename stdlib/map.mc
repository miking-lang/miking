-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the map intrinsics.

include "option.mc"
include "seq.mc"
include "string.mc"


-- Aliases
let mapLength : Map k v -> Int = lam m. mapSize m
let mapLookupOrElse : (Unit -> v) -> k -> Map k v -> v =
  lam f. lam k. lam m.
  mapFindOrElse f k m
let mapLookupApplyOrElse : (v1 -> v2) -> (Unit -> v2) -> k -> Map k v1 -> v2 =
  lam f1. lam f2. lam k. lam m.
  mapFindApplyOrElse f1 f2 k m

let mapIsEmpty : Map k v -> Bool = lam m. eqi (mapSize m) 0

let mapLookup : k -> Map k v -> Option v =
  lam k. lam m.
    mapFindApplyOrElse (lam v. Some v) (lam. None ()) k m

let mapInsertWith : (v -> v -> v) -> k -> v -> Map k v -> Map k v =
  lam f. lam k. lam v. lam m.
    match mapLookup k m with Some prev then
      mapInsert k (f prev v) m
    else mapInsert k v m

let mapUnion : Map k v -> Map k v -> Map k v = lam l. lam r.
  foldl (lam acc. lam binding : (k, v). mapInsert binding.0 binding.1 acc)
        l (mapBindings r)

let mapFromList : (k -> k -> Int) -> [(k, v)] -> Map k v = lam cmp. lam bindings.
  foldl (lam acc. lam binding : (k, v). mapInsert binding.0 binding.1 acc)
        (mapEmpty cmp) bindings

let mapKeys : Map k v -> [k] = lam m.
  mapFoldWithKey (lam ks. lam k. lam. snoc ks k) [] m

let mapValues : Map k v -> [v] = lam m.
  mapFoldWithKey (lam vs. lam. lam v. snoc vs v) [] m

let mapMapAccum : (acc -> k -> v1 -> (acc, v2)) -> acc -> Map k v1 -> (acc, Map k v2) =
  lam f. lam acc. lam m.
    mapFoldWithKey
      (lam tacc : (acc, Map k v2). lam k. lam v1.
         let fval : (acc, v2) = f tacc.0 k v1 in
         match fval with (acc, v2) then (acc, mapInsert k v2 tacc.1) else never)
      (acc, mapEmpty (mapGetCmpFun m)) m

let mapFoldlOption : (acc -> k -> v -> Option acc)
                  -> acc -> Map k v -> Option acc =
  lam f. lam acc. lam m.
    optionFoldlM (lam acc. lam t : (k, v). f acc t.0 t.1) acc (mapBindings m)

let mapAll : (v -> Bool) -> Map k v -> Bool = lam f. lam m.
  mapFoldWithKey (lam acc. lam. lam v. and acc (f v)) true m

mexpr

let m = mapEmpty subi in

utest mapLookupOrElse (lam. 2) 1 m with 2 in
utest mapLookupApplyOrElse (lam. 2) (lam. 3) 1 m with 3 in
utest mapLength m with 0 in
utest mapIsEmpty m with true in

utest mapLookup 1 m with None () using optionEq eqString in

let m = mapInsert 1 "1" m in
let m = mapInsert 2 "2" m in
let m = mapInsert 3 "3" m in

utest mapLength m with 3 in
utest mapIsEmpty m with false in

utest mapLookup 1 m with Some "1" using optionEq eqString in
utest mapLookup 2 m with Some "2" using optionEq eqString in
utest mapLookup 3 m with Some "3" using optionEq eqString in
utest mapLookup 4 m with None () using optionEq eqString in

let m2 = mapInsert 2 "22" m in
let m2 = mapInsert 4 "44" m2 in
let m2 = mapInsert (negi 1) "-1" m2 in

let merged = mapUnion m m2 in
utest mapLookup 1 merged with Some "1" using optionEq eqString in
utest mapLookup 2 merged with Some "22" using optionEq eqString in
utest mapLookup 3 merged with Some "3" using optionEq eqString in
utest mapLookup 4 merged with Some "44" using optionEq eqString in
utest mapLookup (negi 1) merged with Some "-1" using optionEq eqString in
utest mapLookup 5 merged with None () using optionEq eqString in

utest mapFoldlOption (lam acc. lam k. lam v. Some v) 0 m
with Some "3" using optionEq eqString in
utest mapFoldlOption
  (lam acc. lam k. lam v. if eqi k acc then None () else Some acc) 3 m
with None () using optionEq eqString in

let m = mapFromList subi
  [ (1, "1")
  , (2, "2")
  ] in
utest mapLookup 1 m with Some "1" using optionEq eqString in
utest mapLookup 2 m with Some "2" using optionEq eqString in
utest mapLookup 3 m with None () using optionEq eqString in

let m2 = mapInsertWith concat 1 "blub" m in
utest mapLookup 1 m2 with Some "1blub" using optionEq eqString in
utest mapLookup 2 m2 with mapLookup 2 m using optionEq eqString in
utest mapLookup 3 m2 with mapLookup 3 m using optionEq eqString in

utest mapKeys m2 with [1,2] in
utest mapValues m2 with ["1blub","2"] in

utest
match mapMapAccum (lam acc. lam k. lam v. ((addi k acc), concat "x" v)) 0 merged
with (acc, m)
then (acc, mapBindings m)
else never
with (9,[(negi 1,("x-1")),(1,("x1")),(2,("x22")),(3,("x3")),(4,("x44"))]) in

let m = mapFromList subi
  [ (1, "1")
  , (2, "2")
  , (123, "123")
  ] in
utest mapAll (lam str. geqi (length str) 1) m with true in
utest mapAll (lam str. leqi (length str) 3) m with true in
utest mapAll (lam str. lti (length str) 2) m with false in

()
