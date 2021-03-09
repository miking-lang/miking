-- A simple library of functions operating on associative sequences. The
-- difference compared to assoc.mc is that the data type contained here is
-- ordered. With more recently inserted bidings shadowing previous bindings,
-- insertion is O(1). This makes this data type suitable for e.g., evaluation
-- environments and similar.

type AssocSeq k v = [(k, v)]
type AssocTraits k = {eq: k -> k -> Bool}

let assocSeqInsert: k -> v -> AssocSeq k v -> AssocSeq k v =
  lam k. lam v. lam s.
    cons (k,v) s

-- lookup
