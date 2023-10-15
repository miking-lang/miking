-- The collection interface, mostly courtesy of Anders
include "collection-interface.mc"

-- Currently sequence (and string) literals are built-in
-- sequences. Use:
-- * `q` to convert a literal (i.e., something with known, constant,
--   and small length)
-- * `collFromSeq` to convert a `[]` to a `Coll` in all other cases
-- * `seqFromColl` to convert back to a `[]`

-- Here's the example from the paper, with minor name changes, plus `q`

let seqToString
  : all a. (a -> Seq Char) -> Seq a -> Seq Char
  = lam f. lam xs.
    match splitFirst xs with Some (x, xs) then
      let mid = foldl (lam acc. lam x. concat (concat acc (q", ")) (f x)) (f x) xs in
      concat (concat (q"[") mid) (q"]")
    else (q"[]")

mexpr

print (seqFromColl (seqToString (lam x. x) (q[q"a", q"b", q"c"])))
