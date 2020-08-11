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
  nelems : Int,
  eq : k -> k -> Bool,
  hashfn : k -> Int
}

-- Private definitions
let _hashmapDefaultBucketCount = 100
let _hashmapBucketIdx = lam hash. lam hm. modi (absi hash) (length hm.buckets)


-- Returns an empty hashmap with a default number of buckets.
--   eq: A function that specifies equalities between keys in the hashmap.
--   hashfn: A function for computing the hash of a key value.
let hashmapEmpty = lam eq. lam hashfn.
  {buckets = makeSeq _hashmapDefaultBucketCount [],
   nelems = 0,
   eq = eq,
   hashfn = hashfn}

-- An empty hashmap using strings as keys
let hashmapStrEmpty =
  -- An implementation of the djb2 hash function (http://www.cse.yorku.ca/~oz/hash.html)
  recursive let djb2 = lam hash. lam s.
    if null s then
      hash
    else
      let newhash = addi (addi (muli hash 32) hash) (char2int (head s)) in
      djb2 newhash (tail s)
  in
  hashmapEmpty eqstr (djb2 5381)

-- Inserts a value into the hashmap
--   key: The key to bind the value to.
--   value: The value to be inserted.
--   hm: The hashmap to insert the value into.
-- [NOTE]
--   The insertion uses a recursion which is not tail-recursive.
let hashmapInsert = lam key. lam value. lam hm.
  let hash = hm.hashfn key in
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
      else if hm.eq key entry.key then
        cons newEntry (tail seq)
      else
        cons entry (inserter (tail seq))
  in
  let newBucket = inserter bucket in
  -- If lengths differ, then an element has been inserted and we increment nelems
  {{hm with nelems = addi hm.nelems (subi (length newBucket) (length bucket))}
       with buckets = set hm.buckets idx newBucket}

-- Removes a key-value pair from the hashmap
--   key: The key that the value (to be removed) is bound to.
--   hm: The hashmap to remove the pair from.
-- [NOTE]
--   The removal uses a recursion which is not tail-recursive.
let hashmapRemove = lam key. lam hm.
  let hash = hm.hashfn key in
  let idx = _hashmapBucketIdx hash hm in
  let bucket = get hm.buckets idx in
  recursive let remover = lam seq.
    if null seq then
      seq
    else
      let entry = head seq in
      if neqi hash entry.hash then
        cons entry (remover (tail seq))
      else if hm.eq key entry.key then
        tail seq
      else
        cons entry (remover (tail seq))
  in
  let newBucket = remover bucket in
  let newSize = subi hm.nelems (subi (length bucket) (length newBucket)) in
  {{hm with buckets = set hm.buckets idx newBucket}
       with nelems = newSize}

-- Looks up a value in the hashmap, returning an Option type
--   key: The key to be used in the lookup.
--   hm: The hashmap to lookup from.
let hashmapLookupOpt = lam key. lam hm.
  let hash = hm.hashfn key in
  let idx = _hashmapBucketIdx hash hm in
  recursive let finder = lam seq.
    if null seq then
      None ()
    else
      let entry = head seq in
      if neqi hash entry.hash then
        finder (tail seq)
      else if hm.eq key entry.key then
        Some (entry.value)
      else
        finder (tail seq)
  in
  finder (get hm.buckets idx)

-- Same as hashmapLookupOpt, but will return an error if an element was not
-- found instead of returning an Option type.
let hashmapLookup = lam key. lam hm.
  optionGetOrElse (lam _. error "No element in hashmap bound to the specified key.")
                  (hashmapLookupOpt key hm)

-- Checks if a value is bound to the specified key in the hashmap.
--   key: The key to be checked.
--   hm: The hashmap to lookup from.
let hashmapMem = lam key. lam hm.
  optionIsSome (hashmapLookupOpt key hm)


mexpr

let m = hashmapStrEmpty in

utest m.nelems with 0 in
utest hashmapMem "foo" m with false in
utest hashmapLookupOpt "foo" m with None () in

let m = hashmapInsert "foo" "aaa" m in

utest m.nelems with 1 in
utest hashmapMem "foo" m with true in
utest hashmapLookupOpt "foo" m with Some ("aaa") in
utest hashmapLookup "foo" m with "aaa" in

let m = hashmapInsert "bar" "bbb" m in

utest m.nelems with 2 in
utest hashmapMem "bar" m with true in
utest hashmapLookupOpt "bar" m with Some ("bbb") in
utest hashmapLookup "bar" m with "bbb" in

let m = hashmapInsert "foo" "ccc" m in

utest m.nelems with 2 in
utest hashmapMem "foo" m with true in
utest hashmapLookupOpt "foo" m with Some ("ccc") in
utest hashmapLookup "foo" m with "ccc" in

let m = hashmapRemove "foo" m in

utest m.nelems with 1 in
utest hashmapMem "foo" m with false in
utest hashmapLookupOpt "foo" m with None () in

let m = hashmapRemove "foo" m in

utest m.nelems with 1 in
utest hashmapMem "foo" m with false in
utest hashmapLookupOpt "foo" m with None () in

let m = hashmapRemove "babar" m in

utest m.nelems with 1 in
utest hashmapMem "babar" m with false in
utest hashmapLookupOpt "babar" m with None () in

let m = hashmapInsert "" "ddd" m in

utest m.nelems with 2 in
utest hashmapMem "" m with true in
utest hashmapLookupOpt "" m with Some ("ddd") in
utest hashmapLookup "" m with "ddd" in

-- Test with collisions
let n = addi _hashmapDefaultBucketCount 10 in

recursive let populate = lam hm. lam i.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    utest hashmapLookupOpt key hm with None () in
    populate (hashmapInsert key i hm)
             (addi i 1)
in
let m = populate hashmapStrEmpty 0 in

utest m.nelems with n in

recursive let checkmem = lam i.
  if geqi i n then
    ()
  else
    let key = cons 'a' (int2string i) in
    utest hashmapLookupOpt key m with Some (i) in
    checkmem (addi i 1)
in
let _ = checkmem 0 in

recursive let removeall = lam i. lam hm.
  if geqi i n then
    hm
  else
    let key = cons 'a' (int2string i) in
    let newHm = hashmapRemove key hm in
    utest hashmapLookupOpt key newHm with None () in
    removeall (addi i 1) newHm
in
let m = removeall 0 m in

utest m.nelems with 0 in

()
