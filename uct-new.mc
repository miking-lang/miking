include "seq.mc"

type Name

let nameEq : Name -> Name -> Bool = lam. never
let nameSetNewSym : Name -> Name = lam. never
let nameGetStr : Name -> String = lam. never

let fst : all a. all b. (a, b) -> a = lam x. never

type Filter a = [a] -> a -> [a] -> Bool
type Permutation a = [a] -> a -> [a] -> Int

type Eq a
con Eq : all a. (a -> a -> Bool) -> Eq a

-- Properties are normal functions -----------------------------------
let keepAll : all a. Filter a = lam. lam. lam. true
let uniqueKeepLast : all a. Filter a =
  -- TODO(vipa, 2022-10-12): `eq` isn't properly solved yet
  let eq : a -> a -> Bool = lam a. lam b. never a b in
  lam. lam here. lam after.
    not (any (eq here) after)
let uniqueKeepLastKey : all k. all v. Filter (k, v) =
  let eq : (k, v) -> (k, v) -> Bool = lam a. lam b. never a.0 b.0 in
  lam. lam here. lam after.
    not (any (eq here) after)
let insertionOrder : all a. Permutation a = lam pre. lam. lam. length pre

-- Normal collection types are aliases over `Coll` -------------------
type Seq a = Coll (expr keepAll) (expr insertionOrder) a
type MultiSet a = Coll (expr keepAll) _ a
type Set x = Coll (expr uniqueKeepLast) _ x
type Map k v = Coll (expr uniqueKeepLastKey) _ (k, v)

-- Operations are let-bindings with rhs exactly `never` --------------
-- Note that the type annotation is also required --------------------
let insert : all a. all pred. all perm. all pred1. all perm1.
  a -> Coll pred perm a -> Coll pred1 perm1 a
  = never

let empty : all a. all pred. all perm.
  Coll pred perm a
  = never

let fold : all acc. all a. all pred. all perm.
  (acc -> a -> acc) ->
  acc ->
  Coll pred perm a ->
  acc
  = never

let reverse : all a. all pred. all perm.
  Coll pred perm a -> Coll pred perm a
  = never

let findFirstIdx : all a. all pred. all perm.
  (a -> Bool) -> Coll pred perm a -> Option Int
  = never

let lookup : all k. all v. all pred. all perm.
  k -> Coll pred perm (k, v) -> Option v
  = never

let isEmpty : all a. all pred. all perm.
  Coll pred perm a -> Bool
  = never

let map : all a. all b. all pred. all perm.
  (a -> b) -> Coll pred perm a -> Coll pred perm b
  = never

let concat : all a. all pred. all perm. all pred1. all perm1.
  Coll pred perm a -> Coll pred1 perm1 a -> Coll pred perm a
  = never

-- let concatDefault = lam a. lam b.
--   fold (lam acc. lam e. insert e acc) a b

let mapConcat : all a. all b. all pred. all perm. all pred1. all perm1.
  (a -> Coll pred1 perm1 b) -> Coll pred perm a -> Coll pred1 perm1 b
  = never

-- let mapConcatDefault = lam f. lam coll.
--   fold (lam acc. lam a. concat acc (f a)) empty coll

let difference : all a. all pred. all perm. all pred1. all perm1.
  Coll pred perm a -> Coll pred1 perm1 a -> Coll pred perm a
  = never

let nub : all a. all pred. all perm.
  Coll pred perm a -> Coll pred perm a
  = never

let iterateInductively : all a. all pred. all perm. all pred1. all perm1.
  (a -> Coll pred1 perm1 a) -> Coll pred perm a -> Coll pred perm a
  = never

-- let iterateInductivelyDefault = lam f. lam coll.
--   recursive let work = lam prev. lam new.
--     if isEmpty new then prev else
--     let prev = concat prev new in
--     let new = nub (mapConcat (lam a. difference (f a) prev) new) in
--     work prev new
--   in work empty coll

-- Supporting code for examples --------------------------------------
type Expr
con Var : Name -> Expr
con IVar : Int -> Expr
con Lam : (Name, Expr) -> Expr
con App : (Expr, Expr) -> Expr

let smapAccumL = lam f. lam acc. lam e.
  switch e
  case Var _ then (acc, e)
  case IVar _ then (acc, e)
  case Lam (s, e) then
    match f acc e with (acc, e) in
    (acc, Lam (s, e))
  case App (a, b) then
    match f acc a with (acc, a) in
    match f acc b with (acc, b) in
    (acc, App (a, b))
  end

let smap = lam f. lam e. (smapAccumL (lam. lam e. ((), f e)) () e).1
let sfold = lam f. lam acc. lam e. (smapAccumL (lam acc. lam e. (f acc e, e)) acc e).0

-- Example use of some collections, de Bruijn indices ----------------
recursive let debruijn
  : Seq Name -> Expr -> Expr
  = lam env. lam e.
    switch e
    case Lam (n, e) then
      Lam (n, debruijn (insert n env) e)
    case Var n then
      match findFirstIdx (nameEq n) (reverse env)
      with Some idx then IVar idx
      else error "Unbound"
    case e then smap (debruijn env) e
    end
end

-- Example use of some collections, symbolize ------------------------
-- recursive let symbolize
--   : Map String Name -> Expr -> Expr
--   = lam env. lam e.
--     switch e
--     case Lam (n, e) then
--       let n = nameSetNewSym n in
--       Lam (n, symbolize (insert (nameGetStr n, n) env) e)
--     case Var n then
--       match lookup (nameGetStr n) env with Some n
--       then Var n
--       else error "Unbound"
--     case e then smap (symbolize env) e
--     end
-- end

mexpr

debruijn empty (IVar 0);
debruijn empty (IVar 0);
-- symbolize empty (IVar 0);
-- symbolize empty (IVar 0);
()
