-- A simple library of functions operating on associative sequences. The
-- difference compared to assoc.mc is that the data type contained here is
-- ordered. With more recently inserted bindings shadowing previous bindings,
-- insertion is O(1). This makes this data type suitable for e.g., evaluation
-- environments and similar.

include "seq.mc"

type AssocSeq k v = [(k, v)]
type AssocTraits k = {eq: k -> k -> Bool}

let assocSeqEmpty : AssocSeq k v = []

let assocSeqInsert : k -> v -> AssocSeq k v -> AssocSeq k v =
  lam k. lam v. lam s.
    cons (k,v) s

let assocSeqLength : AssocSeq k v -> Int =
  lam s.
    length s

let assocSeqLookup : AssocTraits k -> k -> AssocSeq k v -> Option v =
  lam traits. lam k. lam s.
    optionMapOr (None ())
                (lam t. Some t.1)
                (find (lam t. traits.eq k t.0) s)

let assocSeqMap : (v1 -> v2) -> AssocSeq k v1 -> AssocSeq k v2 =
  lam f. lam s.
    map (lam t. (t.0, f t.1)) s

let assocSeqFold : (acc -> k -> v -> acc) -> acc -> AssocSeq k v -> acc =
  lam f. lam acc. lam s.
    foldl (lam acc. lam kv. f acc kv.0 kv.1) acc s

let seq2assocSeq : [(k, v)] -> AssocSeq k v =
  lam s.
    assocSeqFold (lam acc. lam k. lam v. assocSeqInsert k v acc) assocSeqEmpty s

let assocSeq2seq : AssocSeq k v -> [(k, v)] =
  lam s.
    s
