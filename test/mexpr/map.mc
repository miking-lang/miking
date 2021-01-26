-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Map intrinstics

include "../../stdlib/string.mc"

mexpr

-- TODO
-- mapAny

-- Int map
let m = mapEmpty subi in

let m = mapInsert 1 "1" m in
let m = mapInsert 2 "2" m in
let m = mapInsert 3 "3" m in
let m = mapInsert 4 "4" m in
let m = mapInsert 4 "5" m in

utest mapLookup 1 m with "1" in
utest mapLookup 2 m with "2" in
utest mapLookup 3 m with "3" in
utest mapLookup 4 m with "5" in

utest mapAny (lam k. lam v. eqi 1 k) m with true in
utest mapAny (lam k. lam v. eqString "5" v) m with true in
utest mapAny (lam k. lam v. eqString "4" v) m with false in

-- String-int tuple map
let cmpTuple = lam t1. lam t2.
  let sDiff = cmpString t1.0 t2.0 in
  match sDiff with 0 then
    subi t1.1 t2.1
  else sDiff
in

let m = mapEmpty cmpTuple in

let m = mapInsert ("1", 1) 1 m in
let m = mapInsert ("1", 2) 2 m in
let m = mapInsert ("Hello", 42) 3 m in
let m = mapInsert ("Hello!", 42) 4 m in

utest mapLookup ("1", 1) m with 1 in
utest mapLookup ("1", 2) m with 2 in
utest mapLookup ("Hello", 42) m with 3 in
utest mapLookup ("Hello!", 42) m with 4 in

()
