-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple generic hashmap library.
--
-- TODO(?,?):
--  - Resizing of buckets.
--  - Conversion to and from association lists.
--

include "math.mc"
include "option.mc"
include "string.mc"

-- The base type of a HashMap object.
--   k: Polymorphic key type
--   v: Polymorphic value type
type HashMap k v = {
  buckets : [[{hash : Int, key : k, value : v}]],
  nelems : Int
}
type HashMapTraits k = {
  eq : k -> k -> Bool,
  hashfn : k -> Int
}

-- Private definitions
let _hashmapDefaultBucketCount = 100
let _hashmapBucketIdx = lam hash. lam hm. modi (absi hash) (length hm.buckets)


-- 'hashmapEmpty' is an empty hashmap with a default number of buckets.
let hashmapEmpty : HashMap k v =
  {buckets = makeSeq _hashmapDefaultBucketCount [],
   nelems = 0}

-- 'hashmapStrTraits' is traits for a hashmap with strings as keys.
let hashmapStrTraits : HashMapTraits String v =
  -- An implementation of the djb2 hash function (http://www.cse.yorku.ca/~oz/hash.html)
  recursive let djb2 = lam hash. lam s.
    if null s then
      hash
    else
      let newhash = addi (addi (muli hash 32) hash) (char2int (head s)) in
      djb2 newhash (tail s)
  in
  {eq = eqString, hashfn = djb2 5381}

-- 'hashmapSize' returns the number of elements in a hashmap.
let hashmapSize : HashMap k v = lam hm. hm.nelems

-- 'hashmapInsert traits k v hm' returns a new hashmap, where the key-value pair
-- ('k', 'v') is stored. If 'k' is already a key in 'hm', its old value will be
-- overwritten.
-- [NOTE(?,?)]
--   The insertion uses a recursion that is not tail-recursive.
let hashmapInsert : HashMapTraits k -> k -> v -> HashMap k v -> HashMap k v =
  lam traits. lam key. lam value. lam hm.
    let hash = traits.hashfn key in
    let idx = _hashmapBucketIdx hash hm in
    let bucket = get hm.buckets idx in
    let newEntry = {hash = hash, key = key, value = value} in
    recursive let inserter = lam seq.
      if null seq then
        [newEntry]
      else
        let entry = head seq in
        if neqi hash entry.hash then
          cons entry (inserter (tail seq))
        else if traits.eq key entry.key then
          cons newEntry (tail seq)
        else
          cons entry (inserter (tail seq))
    in
    let newBucket = inserter bucket in
    -- If lengths differ, then an element has been inserted and we increment nelems
    {{hm with nelems = addi hm.nelems (subi (length newBucket) (length bucket))}
         with buckets = set hm.buckets idx newBucket}

-- 'hashmapRemove traits k hm' returns a new hashmap, where 'k' is not a key. If
-- 'k' is not a key in 'hm', the map remains unchanged after the operation.
-- [NOTE(?,?)]
--   The removal uses a recursion that is not tail-recursive.
let hashmapRemove : HashMapTraits k -> k -> HashMap k v -> HashMap k v =
  lam traits. lam key. lam hm.
    let hash = traits.hashfn key in
    let idx = _hashmapBucketIdx hash hm in
    let bucket = get hm.buckets idx in
    recursive let remover = lam seq.
      if null seq then
        seq
      else
        let entry = head seq in
        if neqi hash entry.hash then
          cons entry (remover (tail seq))
        else if traits.eq key entry.key then
          tail seq
        else
          cons entry (remover (tail seq))
    in
    let newBucket = remover bucket in
    let newSize = subi hm.nelems (subi (length bucket) (length newBucket)) in
    {{hm with buckets = set hm.buckets idx newBucket}
         with nelems = newSize}

-- 'hashmapLookup traits k hm' looks up the key 'k' in 'hm', returning an
-- Option type.
let hashmapLookup : HashMapTraits k -> k -> HashMap k v -> Option v =
  lam traits. lam key. lam hm.
    let hash = traits.hashfn key in
    let idx = _hashmapBucketIdx hash hm in
    recursive let finder = lam seq.
      if null seq then
        None ()
      else
        let entry = head seq in
        if neqi hash entry.hash then
          finder (tail seq)
        else if traits.eq key entry.key then
          Some (entry.value)
        else
          finder (tail seq)
    in
    finder (get hm.buckets idx)

-- 'hashmapLookupOrElse traits d k hm': like hashmapLookupOpt, but returns the
-- result of 'd ()' if no element was found.
let hashmapLookupOrElse : HashMapTraits k -> (Unit -> v) -> k -> HashMap k v -> v =
  lam traits. lam d. lam key. lam hm.
    optionGetOrElse d
                    (hashmapLookup traits key hm)

-- 'hashmapLookupOr traits v k hm': like hashmapLookupOpt, but returns the
-- result of 'd ()' if no element was found.
let hashmapLookupOr : HashMapTraits k -> v -> k -> HashMap k v -> v =
  lam traits. lam default.
    hashmapLookupOrElse traits (lam _. default)

-- 'hashmapLookupPred p hm' returns the value of a key that satisfies the
-- predicate 'p'. If several keys satisfies 'p', the one that happens to be
-- found first is returned.
-- [NOTE(?,?)]
--   Linear complexity.
let hashmapLookupPred : (k -> Bool) -> HashMap k v -> Option v =
  lam p. lam hm.
    let flatBuckets = foldr1 concat hm.buckets in
    optionMapOr (None ())
                (lam r. Some (r.value))
                (find (lam r. p r.key) flatBuckets)

-- 'hashmapMem traits k hm' returns true if 'k' is a key in 'hm', else false.
let hashmapMem : HashMapTraits k -> k -> HashMap k v -> Bool =
  lam traits. lam key. lam hm.
    optionIsSome (hashmapLookup traits key hm)

-- 'hashmapAny traits p hm' returns true if at least one entry in the hashmap matches the predicate
let hashmapAny : HashMapTraits k -> (k -> v -> Bool) -> HashMap k v -> Bool =
  lam traits. lam p. lam hm.
    any (any (lam e. p e.key e.value)) hm.buckets

-- 'hashmapAll traits p hm' returns true iff all entries in the hashmap matches the predicate
let hashmapAll : HashMapTraits k -> (k -> v -> Bool) -> HashMap k v -> Bool =
  lam traits. lam p. lam hm.
    all (all (lam e. p e.key e.value)) hm.buckets

-- 'hashmapMap' maps the provided functions on all values in the hashmap
let hashmapMap : HashMapTraits k -> (v1 -> v2) -> HashMap k v1 -> HashMap k v2 =
  lam traits. lam fn. lam hm.
    {buckets = map (map (lam e. {hash = e.hash, key = e.key, value = fn e.value})) hm.buckets,
     nelems = hm.nelems}

-- 'hashmapKeys traits hm' returns a list of all keys stored in 'hm'
let hashmapKeys : HashMapTraits k -> HashMap k v -> [k] =
  lam _. lam hm.
    foldl (lam keys. lam bucket.
             concat keys (map (lam r. r.key) bucket))
          [] hm.buckets

-- 'hashmapValues traits hm' returns a list of all values stored in 'hm'
let hashmapValues : HashMapTraits k -> HashMap k v -> [v] =
  lam _. lam hm.
    foldl (lam vals. lam bucket.
      concat vals (map (lam r. r.value) bucket))
    [] hm.buckets


mexpr

let traits = hashmapStrTraits in
let mem = hashmapMem traits in
let any = hashmapAny traits in
let all = hashmapAll traits in
let map = hashmapMap traits in
let lookupOrElse = hashmapLookupOrElse traits in
let lookupOr = hashmapLookupOr traits in
let lookup = hashmapLookup traits in
let lookupPred = hashmapLookupPred in
let size = hashmapSize in
let insert = hashmapInsert traits in
let remove = hashmapRemove traits in
let keys = hashmapKeys traits in
let values = hashmapValues traits in

let m = hashmapEmpty in

utest size m with 0 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = insert "foo" "aaa" m in

utest size m with 1 in
utest mem "foo" m with true in
utest lookup "foo" m with Some ("aaa") in
utest lookupOrElse (lam _. 42) "foo" m with "aaa" in

let m = insert "bar" "bbb" m in

utest size m with 2 in
utest mem "bar" m with true in
utest any (lam _. lam b. eqString "BBB" (str2upper b)) m with true in
utest any (lam a. lam _. eqString "FOO" (str2upper a)) m with true in
utest any (lam a. lam b. eqString a b) m with false in
utest any (lam a. lam _. eqString "bar" a) m with true in
utest all (lam a. lam _. eqString "bar" a) m with false in
utest all (lam a. lam _. eqi (length a) 3) m with true in
utest all (lam _. lam b. eqi (length b) 3) m with true in
utest lookup "bar" m with Some ("bbb") in
utest lookupOrElse (lam _. "BABAR") "bar" m with "bbb" in
utest lookupOr "bananas" "bar42" m with "bananas" in
utest lookupPred (eqString "bar") m with Some "bbb" in
utest
  match keys m with ["foo", "bar"] | ["bar", "foo"]
  then true else false
with true in
utest
  match values m with ["aaa", "bbb"] | ["bbb", "aaa"]
  then true else false
with true in


-- Test map all values
let mMapped = map (cons '?') m in
utest lookup "foo" mMapped with Some ("?aaa") in
utest lookup "bar" mMapped with Some ("?bbb") in


let m = insert "foo" "ccc" m in

utest size m with 2 in
utest mem "foo" m with true in
utest lookup "foo" m with Some ("ccc") in
utest lookupOrElse (lam _. 42) "foo" m with "ccc" in
utest lookupOrElse (lam _. 42) "abc" m with 42 in

let m = remove "foo" m in

utest size m with 1 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = remove "foo" m in

utest size m with 1 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = remove "babar" m in

utest size m with 1 in
utest mem "babar" m with false in
utest lookup "babar" m with None () in

let m = insert "" "ddd" m in

utest size m with 2 in
utest mem "" m with true in
utest lookup "" m with Some ("ddd") in
utest lookupOrElse (lam _. 1) "" m with "ddd" in

-- Test with collisions
let n = addi _hashmapDefaultBucketCount 10 in

recursive let populate = lam hm. lam i.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    utest lookup key hm with None () in
    populate (insert key i hm)
             (addi i 1)
in
let m = populate (hashmapEmpty) 0 in

utest size m with n in

recursive let checkmem = lam i.
  if geqi i n then
    ()
  else
    let key = cons 'a' (int2string i) in
    utest lookup key m with Some (i) in
    checkmem (addi i 1)
in
let _ = checkmem 0 in

recursive let removeall = lam i. lam hm.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    let newHm = remove key hm in
    utest lookup key newHm with None () in
    removeall (addi i 1) newHm
in
let m = removeall 0 m in

utest size m with 0 in

()
