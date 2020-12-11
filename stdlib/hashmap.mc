-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple generic hashmap library.
--
-- TODO(johnwikman, 2020-08-05): Resizing of buckets.
--
-- NOTE(johnwikman, 2020-10-01): All hashmap functions have the trait argument
-- applied to them, even if they never use it. This is to ensure a more stable
-- API, in case a hashmap trait might be applied for the sake of optimization
-- in a case where it was previously unused.

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

-- 'hashmap2seq hm' converts the hashmap 'hm' to a sequence of tuples.
let hashmap2seq : HashMap k v -> [(k,v)] = lam hm.
  join (map (lam bucket. map (lam e. (e.key, e.value)) bucket)
            hm.buckets)

-- 'hashmapStrTraits' is traits for a hashmap with strings as keys.
let hashmapStrTraits : HashMapTraits String =
  -- An implementation of the djb2 hash function (http://www.cse.yorku.ca/~oz/hash.html)
  recursive let djb2 = lam hash. lam s.
    if null s then
      hash
    else
      let newhash = addi (addi (muli hash 32) hash) (char2int (head s)) in
      djb2 newhash (tail s)
  in
  {eq = eqString, hashfn = djb2 5381}


-- 'hashmapCount hm' returns the number of elements in a hashmap.
let hashmapCount : HashMapTraits k -> HashMap k v -> Int = lam traits. lam hm. hm.nelems

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

-- 'hashmapLookupOrElse traits d key hm': like hashmapLookup, but returns the
-- result of 'd ()' if no element was found.
let hashmapLookupOrElse : HashMapTraits k -> (Unit -> v) -> k -> HashMap k v -> v =
  lam traits. lam d. lam key. lam hm.
    optionGetOrElse d (hashmapLookup traits key hm)

-- 'hashmapLookupOr traits default key hm': like hashmapLookupOrElse, but returns
-- 'default' if no element was found.
let hashmapLookupOr : HashMapTraits k -> v -> k -> HashMap k v -> v =
  lam traits. lam default. lam key. lam hm.
    hashmapLookupOrElse traits (lam _. default) key hm

-- 'hashmapLookupPred p hm' returns the value of a key that satisfies the
-- predicate 'p'. If several keys satisfies 'p', the one that happens to be
-- found first is returned.
-- [NOTE(?,?)]
--   Linear complexity.
let hashmapLookupPred : HashMapTraits k -> (k -> Bool) -> HashMap k v -> Option v =
  lam traits. lam p. lam hm.
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
    any (any (lam r. p r.key r.value)) hm.buckets

-- 'hashmapAll traits p hm' returns true iff all entries in the hashmap matches the predicate
let hashmapAll : HashMapTraits k -> (k -> v -> Bool) -> HashMap k v -> Bool =
  lam traits. lam p. lam hm.
    all (all (lam r. p r.key r.value)) hm.buckets

-- 'hashmapMap' maps the provided functions on all values in the hashmap
let hashmapMap : HashMapTraits k -> (v1 -> v2) -> HashMap k v1 -> HashMap k v2 =
  lam traits. lam fn. lam hm.
    {buckets = map (map (lam r. {hash = r.hash, key = r.key, value = fn r.value})) hm.buckets,
     nelems = hm.nelems}

-- 'hashmapFilter p hm' returns a new hashmap with only the key-value pairs in
-- 'hm' that satisfies 'p'.
let hashmapFilter : HashMapTraits k -> (k -> v -> Bool) -> HashMap k v -> HashMap k v =
  lam traits. lam p. lam hm.
    let ret = foldl (lam acc. lam bucket.
        -- NOTE(johnwikman, 2020-10-01): Using snoc here ensures that order of
        -- the buckets are the same, and that hashing index of all entries remain
        -- valid.
        let newBucket = filter (lam r. p r.key r.value) bucket in
        (snoc acc.0 newBucket, addi acc.1 (length newBucket))
      ) ([], 0) hm.buckets
    in
    {buckets = ret.0, nelems = ret.1}

-- 'hashmapFilterKeys p hm' returns a list of all keys in 'hm' that satisfies 'p'
let hashmapFilterKeys : HashMapTraits k -> (k -> Bool) -> HashMap k v -> [k] =
  lam traits. lam p. lam hm.
    foldl (lam keys. lam bucket.
      concat (map (lam r. r.key)
                  (filter (lam r. p r.key) bucket))
             keys
    ) [] hm.buckets

-- 'hashmapFilterValues traits p hm' returns a list of all values in 'hm' that satisfies 'p'
let hashmapFilterValues : HashMapTraits k -> (v -> Bool) -> HashMap k v -> [v] =
  lam traits. lam p. lam hm.
    foldl (lam values. lam bucket.
      concat (map (lam r. r.value)
                  (filter (lam r. p r.value) bucket))
             values
    ) [] hm.buckets

-- 'hashmapKeys hm' returns a list of all keys stored in 'hm'
let hashmapKeys : HashMapTraits k -> HashMap k v -> [k] =
  lam traits. lam hm.
    hashmapFilterKeys traits (lam _. true) hm

-- 'hashmapValues hm' returns a list of all values stored in 'hm'
let hashmapValues : HashMapTraits k -> HashMap k v -> [v] =
  lam traits. lam hm.
    hashmapFilterValues traits (lam _. true) hm


mexpr

let empty = hashmapEmpty in
let traits = hashmapStrTraits in
let mem = hashmapMem traits in
let any = hashmapAny traits in
let all = hashmapAll traits in
let map = hashmapMap traits in
let filter = hashmapFilter traits in
let filterKeys = hashmapFilterKeys traits in
let filterValues = hashmapFilterValues traits in
let lookupOrElse = hashmapLookupOrElse traits in
let lookupOr = hashmapLookupOr traits in
let lookup = hashmapLookup traits in
let lookupPred = hashmapLookupPred traits in
let count = hashmapCount traits in
let insert = hashmapInsert traits in
let remove = hashmapRemove traits in
let keys = hashmapKeys traits in
let values = hashmapValues traits in

let m = empty in

utest count m with 0 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = insert "foo" "aaa" m in

utest count m with 1 in
utest mem "foo" m with true in
utest lookup "foo" m with Some ("aaa") in
utest lookupOrElse (lam _. 42) "foo" m with "aaa" in

let m = insert "bar" "bbb" m in

utest count m with 2 in
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
utest
  match hashmap2seq m with [("foo", "aaa"), ("bar", "bbb")] | [("bar", "bbb"), ("foo", "aaa")]
  then true else false
with true in
utest filter (eqString) m with empty in
utest hashmap2seq (filter (lam a. lam _. eqString "foo" a) m) with [("foo", "aaa")] in
utest hashmap2seq (filter (lam _. lam b. eqString "bbb" b) m) with [("bar", "bbb")] in
utest filterKeys (lam a. optionIsSome (strIndex 'o' a)) m with ["foo"] in
utest filterValues (lam a. optionIsSome (strIndex 'b' a)) m with ["bbb"] in


-- Test map all values
let mMapped = map (cons '?') m in
utest lookup "foo" mMapped with Some ("?aaa") in
utest lookup "bar" mMapped with Some ("?bbb") in


let m = insert "foo" "ccc" m in

utest count m with 2 in
utest mem "foo" m with true in
utest lookup "foo" m with Some ("ccc") in
utest lookupOrElse (lam _. 42) "foo" m with "ccc" in
utest lookupOrElse (lam _. 42) "abc" m with 42 in

let m = remove "foo" m in

utest count m with 1 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = remove "foo" m in

utest count m with 1 in
utest mem "foo" m with false in
utest lookup "foo" m with None () in

let m = remove "babar" m in

utest count m with 1 in
utest mem "babar" m with false in
utest lookup "babar" m with None () in

let m = insert "" "ddd" m in

utest count m with 2 in
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
let m = populate (empty) 0 in

utest count m with n in

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

utest count m with 0 in

()
