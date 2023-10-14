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
