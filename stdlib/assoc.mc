-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple library that defines map operations over sequences of tuples.

include "option.mc"
include "set.mc"
include "char.mc"

type AssocMap k v = [(k, v)]
type AssocTraits k = {eq : k -> k -> Bool}

-- 'assocEmpty' is an empty associate map
let assocEmpty : AssocMap k v =
  []

-- 'assocLength m' returns the number of key-value pairs in m
let assocLength : AssocMap k v -> Int =
  length

-- 'assocInsert traits k v m' returns a new map, where the key-value pair
-- ('k','v') is stored. If 'k' is already a key in 'm', its old value will be
-- overwritten.
let assocInsert : AssocTraits k -> k -> v -> AssocMap k v -> AssocMap k v =
  lam traits. lam k. lam v. lam m.
    -- PERFORMANCE
    -- optionMapOrElse (lam _. cons (k,v) m)
    --                 (lam i. set m i (k,v))
    --                 (index (lam t. traits.eq k t.0) m)
    cons (k,v) m

-- 'seq2assoc traits ls' constructs a new association map from a sequence
-- of tuples 'ls'. Bindings to the right overwrites previous equal bindings to
-- the left.
let seq2assoc : AssocTraits k -> [(k,v)] -> AssocMap k v =
  lam traits. lam ls.
    foldl (lam acc. lam t. assocInsert traits t.0 t.1 acc) assocEmpty ls

-- 'assoc2seq traits m' constructs a new sequence of tuples representing the association map 'm'.
-- The order of the elements in the sequence is unspecified.
let assoc2seq : AssocTraits k -> AssocMap k v -> [(k,v)] =
  lam traits. lam m.
    m

-- 'assocRemove traits k m' returns a new map, where 'k' is not a key. If 'k' is
-- not a key in 'm', the map remains unchanged after the operation.
let assocRemove : AssocTraits k -> k -> AssocMap k v -> AssocMap k v =
  lam traits. lam k. lam m.
    optionMapOr m
                (lam i.
                  let spl = splitAt m i in
                  concat spl.0 (tail spl.1))
                (index (lam t. traits.eq k t.0) m)


-- 'assocLookup traits k m' looks up the key 'k' and returns an Option type.
-- If 'm' has the key 'k' stored, its value is returned, otherwise None () is
-- returned.
let assocLookup : AssocTraits k -> k -> AssocMap k v -> Option v =
  lam traits. lam k. lam m.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. traits.eq k t.0) m)

-- 'assocLookupOrElse traits d k m' returns the value of key 'k' in 'm' if it
-- exists, otherwise returns the result of 'd ()'.
let assocLookupOrElse : AssocTraits k -> (Unit -> v) -> k -> AssocMap k v -> v =
  lam traits. lam d. lam k. lam m.
    optionGetOrElse d
                    (assocLookup traits k m)

-- 'assocLookupPred p m' returns the associated value of a key that satisfies
-- the predicate 'p'. If several keys satisfies 'p', the one that happens to be
-- found first is returned.
let assocLookupPred : (k -> Bool) -> AssocMap k v -> Option v =
  lam p. lam m.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. p t.0) m)

-- 'assocAny p m' returns true if at least one (k,v) pair in the map satisfies
-- the predicate 'p'.
let assocAny : (k -> v -> Bool) -> AssocMap k v -> Bool =
  lam p. lam m.
    any (lam t. p t.0 t.1) m

-- 'assocAll p m' returns true if all (k,v) pair in the map satisfies
-- the predicate 'p'.
let assocAll : (k -> v -> Bool) -> AssocMap k v -> Bool =
  lam p. lam m.
    all (lam t. p t.0 t.1) m

-- 'assocMem traits k m' returns true if 'k' is a key in 'm', else false.
let assocMem : AssocTraits k -> k -> AssocMap k v -> Bool =
  lam traits. lam k. lam m.
    optionIsSome (assocLookup traits k m)

-- 'assocKeys traits m' returns a list of all keys stored in 'm'
let assocKeys : AssocTraits k -> AssocMap k v -> [k] =
  lam _. lam m.
    map (lam t. t.0) m

-- 'assocValues traits m' returns a list of all values stored in 'm'
let assocValues : AssocTraits k -> AssocMap k v -> [v] =
  lam _. lam m.
    map (lam t. t.1) m

-- 'assocMap traits f m' maps over the values of 'm' using function 'f'.
let assocMap : AssocTraits k -> (v1 -> v2) -> AssocMap k v1 -> AssocMap k v2 =
  lam _. lam f. lam m.
    map (lam t. (t.0, f t.1)) m

-- 'assocMapWithKey f m' maps over the values of 'm' using function 'f', where 'f' additionally has access to the key of the value being operated upon.
let assocMapWithKey : AssocTraits k -> (k -> v1 -> v2) -> AssocMap k v1 -> AssocMap k v2 =
  lam _. lam f. lam m.
    map (lam t. (t.0, f t.0 t.1)) m

-- 'assocFold traits f acc m' folds over 'm' using function 'f' and accumulator
-- 'acc'.
-- IMPORTANT: The folding order is unspecified.
let assocFold : AssocTraits k -> (acc -> k -> v -> acc)
                  -> acc -> AssocMap k v -> acc =
  lam _. lam f. lam acc. lam m.
    foldl (lam acc. lam t. f acc t.0 t.1) acc m

-- 'assocFoldlM traits f acc m' folds over 'm' using function 'f' and accumulator
-- 'acc'. The folding stops immediately if 'f' returns 'None ()'.
-- IMPORTANT: The folding order is unspecified.
let assocFoldlM : AssocTraits k -> (acc -> k -> v -> Option acc)
                        -> acc -> AssocMap k v -> Option acc =
  lam _. lam f. lam acc. lam m.
    optionFoldlM (lam acc. lam t. f acc t.0 t.1) acc m

-- 'assocMapAccum traits f acc m' simultaneously performs a map (over values)
-- and fold over 'm' using function 'f' and accumulator 'acc'.
-- IMPORTANT: The folding order is unspecified.
let assocMapAccum : AssocTraits k -> (acc -> k -> v1 -> (acc, v2))
                      -> acc -> AssocMap k v1 -> (acc, AssocMap k v2) =
  lam _. lam f. lam acc. lam m.
    mapAccumL
      (lam acc. lam t.
         match f acc t.0 t.1 with (acc, b) then (acc, (t.0, b)) else never)
      acc m

-- 'assocMergePreferRight traits l r' merges two maps, keeping values from r in case a key
-- exists in both maps. See also 'assocMergePreferLeft'
let assocMergePreferRight : AssocTraits k -> AssocMap k v -> AssocMap k v -> AssocMap k v =
  lam traits. lam l. lam r.
    assocFold traits (lam m. lam k. lam v. assocInsert traits k v m) l r

-- 'assocMergePreferLeft traits l r' merges two maps, keeping values from l in case a key
-- exists in both maps. See also 'assocMergePreferRight'
let assocMergePreferLeft : AssocTraits k -> AssocMap k v -> AssocMap k v -> AssocMap k v =
  lam traits. lam l. lam r. assocMergePreferRight traits r l

mexpr

let traits = {eq = eqi} in

let length = assocLength in
let lookup = assocLookup traits in
let lookupOrElse = assocLookupOrElse traits in
let lookupPred = assocLookupPred in
let any = assocAny in
let all = assocAll in
let insert = assocInsert traits in
let seq2assoc = seq2assoc traits in
let assoc2seq = assoc2seq traits in
let mem = assocMem traits in
let remove = assocRemove traits in
let keys = assocKeys traits in
let values = assocValues traits in
let map = assocMap traits in
let mapWithKey = assocMapWithKey traits in
let fold = assocFold traits in
let foldOption = assocFoldlM traits in
let mapAccum = assocMapAccum traits in
let mergePreferLeft = assocMergePreferLeft traits in
let mergePreferRight = assocMergePreferRight traits in

let m = assocEmpty in
let m = insert 1 '1' m in
let m = insert 2 '2' m in
let m = insert 3 '3' m in

utest length m with 3 in
utest lookup 1 m with Some '1' in
utest lookup 2 m with Some '2' in
utest lookup 3 m with Some '3' in
utest lookup 4 m with None () in
utest lookupOrElse (lam _. 42) 1 m with '1' in
utest lookupOrElse (lam _. 42) 2 m with '2' in
utest lookupOrElse (lam _. 42) 3 m with '3' in
utest lookupPred (eqi 2) m with Some '2' in
utest any (lam k. lam v. eqChar v '2') m with true in
utest any (lam k. lam v. eqChar v '4') m with false in
utest all (lam k. lam v. gti k 0) m with true in
utest all (lam k. lam v. gti k 1) m with false in
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

utest sort (lam l. lam r. subi l.0 r.0) (assoc2seq m)
with [(1, '1'), (2, '2'), (3, '3')] in

let withKeyMap = mapWithKey (lam k. lam v. (k, v)) m in
utest lookup 1 withKeyMap with Some (1, '1') in
utest lookup 2 withKeyMap with Some (2, '2') in
utest lookup 3 withKeyMap with Some (3, '3') in

let nextChar = lam c. int2char (addi 1 (char2int c)) in

let mapm = (map nextChar m) in
utest (lookup 1 mapm, lookup 2 mapm, lookup 3 mapm)
with (Some '2', Some '3', Some '4') in

utest fold (lam acc. lam k. lam v. addi acc k) 0 m with 6 in
utest fold (lam acc. lam k. lam v. and acc (isDigit v)) true m with true in

utest foldOption (lam acc. lam k. lam v. Some (addi acc k)) 0 m with Some 6 in
utest foldOption (lam acc. lam k. lam v. if eqi k 4 then None () else Some acc)
        true m
with Some true in
utest foldOption (lam acc. lam k. lam v. if eqi k 2 then None () else Some acc)
        true m
with None () in

let mapaccm = mapAccum (lam acc. lam k. lam v. (addi acc k, nextChar v)) 0 m in
utest (mapaccm.0, (lookup 1 mapaccm.1, lookup 2 mapaccm.1, lookup 3 mapaccm.1))
with (6, (Some '2', Some '3', Some '4')) in

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

let m1 = insert 1 "1l" (insert 2 "2l" assocEmpty) in
let m2 = insert 1 "1r" (insert 3 "3r" assocEmpty) in
let ml = mergePreferLeft m1 m2 in
let mr = mergePreferRight m1 m2 in

utest ml with mergePreferRight m2 m1 in
utest lookup 1 ml with Some "1l" in
utest lookup 2 ml with Some "2l" in
utest lookup 3 ml with Some "3r" in

utest mr with mergePreferLeft m2 m1 in
utest lookup 1 mr with Some "1r" in
utest lookup 2 mr with Some "2l" in
utest lookup 3 mr with Some "3r" in

()
