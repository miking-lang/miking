-------------------------------
-- Ropes (builtin sequences) --
-------------------------------

type Rope a = [a]

let ropeEmpty = []
let ropeAppend = lam xs. lam x. snoc xs x
let ropePrepend = lam x. lam xs. cons x xs
let ropeFoldl = lam f. lam acc. lam c. foldl f acc c
let ropeFoldr = lam f. lam acc. lam c. foldr f acc c
let ropeConcat = lam a. lam b. concat a b
let ropeLength = lam xs. length xs
let ropePartition : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam p. lam seq.
  recursive let work = lam l. lam r. lam seq.
    match seq with [] then (l, r)
    else match seq with [s] ++ seq then
      if p s then work (cons s l) r seq
      else work l (cons s r) seq
    else never
  in work [] [] (reverse seq)

recursive
let ropeQuickSortBy : all a. (a -> a -> Int) -> ([a] -> [a]) = lam cmp. lam seq.
  if null seq then seq else
    let h = head seq in
    let t = tail seq in
    let lr = ropePartition (lam x. lti (cmp x h) 0) t in
    concat (ropeQuickSortBy cmp lr.0) (cons h (ropeQuickSortBy cmp lr.1))
end

---------------
-- Cons-list --
---------------

type ConsList a
con CLCons : all a. (a, ConsList a) -> ConsList a
con CLNil : all a. () -> ConsList a

let consEmpty = CLNil ()
let consPrepend = lam x. lam xs. CLCons (x, xs)
let consFoldr = lam f. lam acc. lam xs.
  recursive let work = lam xs.
    switch xs
    case CLNil _ then acc
    case CLCons (x, xs) then f x (work xs)
    end
  in work xs
let consFoldl = lam f. lam acc. lam xs.
  recursive let work = lam acc. lam xs.
    switch xs
    case CLNil _ then acc
    case CLCons (x, xs) then work (f acc x) xs
    end
  in work acc xs
let consAppend = lam xs. lam x. consFoldr consPrepend (CLCons (x, consEmpty)) xs
let consUncons = lam xs. match xs with CLCons ret then Some ret else None ()
