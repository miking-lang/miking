-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- A simple generic hashmap library.
--
-- TODO:
--  - Resizing of buckets.
--  - Conversion to and from association lists.
--

include "math.mc"
include "option.mc"
include "string.mc"

-- The base type of a HashMap object.
--   k: Polymorphic key type
--   v: Polymorphic value type
type HashMap = {
  buckets : [[{hash : Int, key : k, value : v}]],
  nelems : Int
}
type HashMapTraits = {
  eq : k -> k -> Bool,
  hashfn : k -> Int
}

-- Private definitions
let _hashmapDefaultBucketCount = 100
let _hashmapBucketIdx = lam hash. lam hm. modi (absi hash) (length hm.buckets)


-- 'hashmapEmpty ()' returns an empty hashmap with a default number of buckets.
let hashmapEmpty : Unit -> HashMap = lam _.
  {buckets = makeSeq _hashmapDefaultBucketCount [],
   nelems = 0}

-- 'hashmapStrTraits' is traits for a hashmap with strings as keys.
let hashmapStrTraits : HashMapTraits =
  -- An implementation of the djb2 hash function (http://www.cse.yorku.ca/~oz/hash.html)
  recursive let djb2 = lam hash. lam s.
    if null s then
      hash
    else
      let newhash = addi (addi (muli hash 32) hash) (char2int (head s)) in
      djb2 newhash (tail s)
  in
  {eq = eqstr, hashfn = djb2 5381}

-- 'hashmapInsert traits k v hm' returns a new hashmap, where the key-value pair
-- ('k', 'v') is stored. If 'k' is already a key in 'hm', its old value will be
-- overwritten.
-- [NOTE]
--   The insertion uses a recursion that is not tail-recursive.
let hashmapInsert : HashMapTraits -> k -> v -> HashMap -> HashMap =
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
-- [NOTE]
--   The removal uses a recursion that is not tail-recursive.
let hashmapRemove : HashMapTraits -> k -> HashMap -> HashMap =
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

-- 'hashmapLookupOpt traits k hm' looks up the key 'k' in 'hm', returning an
-- Option type.
let hashmapLookupOpt : HashMapTraits -> k -> HashMap -> OptionV =
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

-- 'hashmapLookup traits k hm': like hashmapLookupOpt, but will return an error
-- if an element was not found instead of returning an Option type.
let hashmapLookup : HashMapTraits -> k -> HashMap -> v =
  lam traits. lam key. lam hm.
    optionGetOrElse (lam _. error "No element in hashmap bound to the specified key.")
                    (hashmapLookupOpt traits key hm)

-- 'hashmapMem traits k hm' returns true if 'k' is a key in 'hm', else false.
let hashmapMem : HashMapTraits -> k -> HashMap -> Bool =
  lam traits. lam key. lam hm.
    optionIsSome (hashmapLookupOpt traits key hm)


mexpr

let traits = hashmapStrTraits in
let mem = hashmapMem traits in
let lookup = hashmapLookup traits in
let lookupOpt = hashmapLookupOpt traits in
let insert = hashmapInsert traits in
let remove = hashmapRemove traits in

let m = hashmapEmpty () in

utest m.nelems with 0 in
utest mem "foo" m with false in
utest lookupOpt "foo" m with None () in

let m = insert "foo" "aaa" m in

utest m.nelems with 1 in
utest mem "foo" m with true in
utest lookupOpt "foo" m with Some ("aaa") in
utest lookup "foo" m with "aaa" in

let m = insert "bar" "bbb" m in

utest m.nelems with 2 in
utest mem "bar" m with true in
utest lookupOpt "bar" m with Some ("bbb") in
utest lookup "bar" m with "bbb" in

let m = insert "foo" "ccc" m in

utest m.nelems with 2 in
utest mem "foo" m with true in
utest lookupOpt "foo" m with Some ("ccc") in
utest lookup "foo" m with "ccc" in

let m = remove "foo" m in

utest m.nelems with 1 in
utest mem "foo" m with false in
utest lookupOpt "foo" m with None () in

let m = remove "foo" m in

utest m.nelems with 1 in
utest mem "foo" m with false in
utest lookupOpt "foo" m with None () in

let m = remove "babar" m in

utest m.nelems with 1 in
utest mem "babar" m with false in
utest lookupOpt "babar" m with None () in

let m = insert "" "ddd" m in

utest m.nelems with 2 in
utest mem "" m with true in
utest lookupOpt "" m with Some ("ddd") in
utest lookup "" m with "ddd" in

-- Test with collisions
let n = addi _hashmapDefaultBucketCount 10 in

recursive let populate = lam hm. lam i.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    utest lookupOpt key hm with None () in
    populate (insert key i hm)
             (addi i 1)
in
let m = populate (hashmapEmpty ()) 0 in

utest m.nelems with n in

recursive let checkmem = lam i.
  if geqi i n then
    ()
  else
    let key = cons 'a' (int2string i) in
    utest lookupOpt key m with Some (i) in
    checkmem (addi i 1)
in
let _ = checkmem 0 in

recursive let removeall = lam i. lam hm.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    let newHm = remove key hm in
    utest lookupOpt key newHm with None () in
    removeall (addi i 1) newHm
in
let m = removeall 0 m in

utest m.nelems with 0 in

()
