-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Map intrinstics

mexpr

-- Int map
let m = mapEmpty subi in

let m = mapInsert 1 '1' m in
let m = mapInsert 2 '2' m in
let m = mapInsert 3 '3' m in
let m = mapInsert 4 '4' m in
let m = mapInsert 4 '5' m in

utest mapFind 1 m with '1' in
utest mapFind 2 m with '2' in
utest mapFind 3 m with '3' in
utest mapFind 4 m with '5' in

utest mapMem 1 m with true in
utest mapMem 42 m with false in

utest mapAny (lam k. lam v. eqi 1 k) m with true in
utest mapAny (lam k. lam v. eqi (char2int '5') (char2int v)) m with true in
utest mapAny (lam k. lam v. eqi (char2int '4') (char2int v)) m with false in

-- Int tuple map
let cmpTuple = lam t1. lam t2.
  let d = subi t1.0 t2.0 in
  match d with 0 then
    subi t1.1 t2.1
  else d
in

let m = mapEmpty cmpTuple in

let m = mapInsert (1, 1) 1 m in
let m = mapInsert (1, 1) 2 m in
let m = mapInsert (1, 2) 2 m in
let m = mapInsert (2, 42) 3 m in
let m = mapInsert (3, 42) 4 m in

utest mapFind (1, 1) m with 2 in
utest mapFind (1, 2) m with 2 in
utest mapFind (2, 42) m with 3 in
utest mapFind (3, 42) m with 4 in

()
