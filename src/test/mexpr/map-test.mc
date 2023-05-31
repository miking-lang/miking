-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Map intrinstics

include "char.mc"
include "map.mc"
include "seq.mc"

mexpr

-- Int map
let m = mapEmpty subi in

utest (mapGetCmpFun m) 2 1 with 1 in

utest mapSize m with 0 in

let m = mapInsert 1 '1' m in
let m = mapInsert 2 '2' m in
let m = mapInsert 3 '3' m in
let m = mapInsert 4 '4' m in
let m = mapInsert 4 '5' m in

utest mapSize m with 4 in

utest mapFindExn 1 m with '1' in
utest mapFindExn 2 m with '2' in
utest mapFindExn 3 m with '3' in
utest mapFindExn 4 m with '5' in

utest mapFindOrElse (lam. '0') 1 m with '1' in
utest mapFindOrElse (lam. '0') 2 m with '2' in
utest mapFindOrElse (lam. '0') 3 m with '3' in
utest mapFindOrElse (lam. '0') 4 m with '5' in
utest mapFindOrElse (lam. '0') 5 m with '0' in

utest mapFindApplyOrElse char2int (lam. 0) 1 m with 49 in
utest mapFindApplyOrElse char2int (lam. 0) 2 m with 50 in
utest mapFindApplyOrElse char2int (lam. 0) 5 m with 0 in

utest mapMem 1 m with true in
utest mapMem 42 m with false in

utest mapAny (lam k. lam v. eqi 1 k) m with true in
utest mapAny (lam k. lam v. eqi (char2int '5') (char2int v)) m with true in
utest mapAny (lam k. lam v. eqi (char2int '4') (char2int v)) m with false in

utest mapBindings m with [(1,'1'), (2,'2'), (3,'3'), (4,'5')] in

utest
  match mapChooseExn m with (k, v) then
    and (mapMem k m) (eqChar (mapFindExn k m) v)
  else never
with true in

utest
  match mapChooseOrElse (lam. error "impossible") m with (k, v) then
    and (mapMem k m) (eqChar (mapFindExn k m) v)
  else never
with true in

utest mapChooseOrElse (lam. (0, '0')) (mapEmpty subi)
with (0, '0') in

let bindsSort = sort (lam t1 : (Int, Char). lam t2 : (Int, Char). subi t1.0 t2.0) in

let m = mapMap (lam c. int2char (addi 1 (char2int c))) m in
utest bindsSort (mapBindings m) with [(1,'2'), (2,'3'), (3,'4'), (4,'6')] in

let m = mapMapWithKey (lam k. lam v. int2char (addi k (char2int v))) m in
utest bindsSort (mapBindings m) with [(1,'3'), (2,'5'), (3,'7'), (4,':')] in

utest mapFoldWithKey (lam acc. lam k. lam v. addi (addi k acc) (char2int v)) 0 m
with 227 in

-- Int tuple map
let cmpTuple = lam t1 : (Int, Int). lam t2 : (Int, Int).
  let d = subi t1.0 t2.0 in
  match d with 0 then
    subi t1.1 t2.1
  else d
in

let m = mapEmpty cmpTuple in

utest (mapGetCmpFun m) (1, 1) (1, 2) with negi 1 in

let m = mapInsert (1, 1) 1 m in
let m = mapInsert (1, 1) 2 m in
let m = mapInsert (1, 2) 2 m in
let m = mapInsert (2, 42) 3 m in
let m = mapInsert (3, 42) 4 m in

utest mapFindExn (1, 1) m with 2 in
utest mapFindExn (1, 2) m with 2 in
utest mapFindExn (2, 42) m with 3 in
utest mapFindExn (3, 42) m with 4 in

-- NOTE(dlunde,2021-03-04): mapEq and mapCmp are a bit hazardous, since the compare
-- function for keys bundled with the first map is always used when doing the
-- comparison. I assume we only use this as a temporary solution (I'm not sure
-- how this would be type checked otherwise)
utest mapEq eqi m m with true in
utest mapEq neqi m m with false in
utest mapEq eqi (mapInsert (2,2) 42 m) m with false in
utest mapCmp subi m m with 0 in
utest mapCmp subi (mapInsert (2,2) 42 m) m with negi 40 in
utest mapCmp subi m (mapInsert (2,2) 42 m) with 40 in

()
