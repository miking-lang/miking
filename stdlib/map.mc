-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the map intrinsics.

include "option.mc"

let mapLookup : k -> Map k v -> Option v =
  lam k. lam m.
    match mapMem k m with false then None ()
    else Some (mapFind k m)

let mapUnion : Map k v -> Map k v -> Map k v = lam l. lam r.
  foldl (lam acc. lam binding. mapInsert binding.0 binding.1 acc) l (mapBindings r)

mexpr

let m = mapEmpty subi in

utest mapLookup 1 m with None () in

let m = mapInsert 1 "1" m in
let m = mapInsert 2 "2" m in
let m = mapInsert 3 "3" m in

utest mapLookup 1 m with Some "1" in
utest mapLookup 2 m with Some "2" in
utest mapLookup 3 m with Some "3" in
utest mapLookup 4 m with None () in

let m2 = mapInsert 2 "22" m in
let m2 = mapInsert 4 "44" m2 in
let m2 = mapInsert (negi 1) "-1" m2 in

let merged = mapUnion m m2 in
utest mapLookup 1 merged with Some "1" in
utest mapLookup 2 merged with Some "22" in
utest mapLookup 3 merged with Some "3" in
utest mapLookup 4 merged with Some "44" in
utest mapLookup (negi 1) merged with Some "-1" in
utest mapLookup 5 merged with None () in

()
