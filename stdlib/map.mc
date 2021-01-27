-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the map intrinsics.

let mapLookup : k -> Map k v -> Option v =
  lam k. lam m.
    match mapMem k m with false then None ()
    else Some (mapFind k m)

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

()
