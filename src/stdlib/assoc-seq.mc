-- A simple library of functions operating on associative sequences. The
-- difference compared to assoc.mc is that the data type contained here is
-- ordered. With more recently inserted bindings shadowing previous bindings,
-- insertion is O(1). This makes this data type suitable for e.g., evaluation
-- environments and similar.

include "seq.mc"

type AssocSeq k v = [(k, v)]
type AssocTraits k = {eq: k -> k -> Bool}

let assocSeqInsert : all k. all v. k -> v -> AssocSeq k v -> AssocSeq k v =
  lam k. lam v. lam s.
    cons (k,v) s

let assocSeqLookup : all k. all v. AssocTraits k -> k -> AssocSeq k v -> Option v =
  lam traits : {eq : k -> k -> Bool}. lam k. lam s.
    optionMapOr (None ())
                (lam t : (k, v). Some t.1)
                (find (lam t : (k, v). traits.eq k t.0) s)

let assocSeqReverseLookup : all k. all v. AssocTraits v -> v -> AssocSeq k v -> Option k =
  lam revTraits : {eq : v -> v -> Bool}. lam v. lam s.
    optionMapOr (None ())
                (lam t : (k, v). Some t.0)
                (find (lam t : (k, v). revTraits.eq v t.1) s)

let assocSeqMap : all k. all v1. all v2. (v1 -> v2) -> AssocSeq k v1 -> AssocSeq k v2 =
  lam f. lam s.
    map (lam t : (k, v1). (t.0, f t.1)) s

let assocSeqFold : all acc. all k. all v.
  (acc -> k -> v -> acc) -> acc -> AssocSeq k v -> acc =
  lam f. lam acc. lam s.
    foldl (lam acc. lam kv : (k, v). f acc kv.0 kv.1) acc s
