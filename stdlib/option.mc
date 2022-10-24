include "bool.mc"

type Option a
con Some : all a. a -> Option a
con None : all a. () -> Option a

-- Equality check between two options. Returns true if both are None, false if
-- exactly one of them are None, and the result of evaluating the provided
-- equality function if both are Some.
let optionEq: all a. all b. (a -> b -> Bool) -> Option a -> Option b -> Bool =
  lam eq. lam o1. lam o2.
    match (o1, o2) with (Some v1, Some v2) then
      eq v1 v2
    else match (o1, o2) with (None (), None ()) then
      true
    else
      false

utest optionEq eqi (Some 10) (Some 10) with true
utest optionEq eqi (Some 10) (Some 11) with false
utest optionEq eqi (Some 10) (None ()) with false
utest optionEq eqi (None ()) (None ()) with true

-- Applies a function to the contained value (if any).
let optionMap: all a. all b. (a -> b) -> Option a -> Option b = lam f. lam o.
  match o with Some t then
    Some (f t)
  else
    None ()

utest optionMap (addi 1) (None ()) with (None ()) using optionEq eqi
utest optionMap (addi 1) (Some 1) with (Some 2) using optionEq eqi

let optionMapAccum: all a. all b. all acc.
  (acc -> a -> (acc, b)) -> acc -> Option a -> (acc, Option b) =
  lam f. lam acc. lam o.
    match o with Some a then
      match f acc a with (acc, b) then
        (acc, Some b)
      else never
    else (acc, None ())

utest optionMapAccum (lam acc. lam a. (acc, a)) () (Some 5) with ((), Some 5)

-- TODO(vipa, 2021-05-28): Write tests for optionMapAccum

let optionJoin: all a. Option (Option a) -> Option a = lam o.
    match o with Some t then
      t
    else
      None ()

utest optionJoin (Some (Some 1)) with (Some 1) using optionEq eqi
utest optionJoin (Some (None ())) with (None ()) using optionEq eqi
utest optionJoin (None ()) with (None ()) using optionEq eqi

-- Returns `None` if the option is `None`, otherwise calls the
-- specified function on the wrapped value and returns the result.
let optionBind: all a. all b. Option a -> (a -> Option b) -> Option b =
  lam o. lam f.
  optionJoin (optionMap f o)

utest optionBind (None ()) (lam t. Some (addi 1 t)) with (None ()) using optionEq eqi
utest optionBind (Some 1) (lam t. Some (addi 1 t)) with (Some 2) using optionEq eqi
utest optionBind (Some 1) (lam. None ()) with (None ()) using optionEq eqi

-- 'optionCompose f g' composes the option-producing functions 'f' and 'g' into
-- a new function, which only succeeds if both 'f' and 'g' succeed.
let optionCompose: all a. all b. all c.
  (b -> Option c) -> (a -> Option b) -> a -> Option c =
  lam f. lam g. lam x.
    optionBind (g x) f

utest optionCompose (lam t. Some (addi 1 t)) (lam t. Some (muli 2 t)) 2 with Some 5 using optionEq eqi
utest optionCompose (lam t. None ()) (lam t. Some (muli 2 t)) 2 with None () using optionEq eqi
utest optionCompose (lam t. Some (addi 1 t)) (lam t. None ()) 2 with None () using optionEq eqi

-- 'optionZipWith f o1 o2' applies the function f on the values contained in
-- o1 and o2. If either o1 or o2 is None, then None is returned.
let optionZipWith: all a. all b. all c.
  (a -> b -> c) -> (Option a) -> (Option b) -> Option c =
  lam f. lam o1. lam o2.
    match (o1, o2) with (Some v1, Some v2) then
      Some (f v1 v2)
    else
      None ()

utest optionZipWith muli (Some 2) (Some 3) with Some 6 using optionEq eqi
utest optionZipWith muli (Some 2) (None ()) with None () using optionEq eqi
utest optionZipWith muli (None ()) (None ()) with None () using optionEq eqi

-- 'optionZipWithOrElse d f o1 o2' applies the function f on the values
-- contained in o1 and o2. If either o1 or o2 is None, then d is evaluated to
-- produce a default value.
let optionZipWithOrElse: all a. all b. all c.
  (() -> c) -> (a -> b -> c) -> (Option a) -> (Option b) -> c =
  lam d. lam f. lam o1. lam o2.
    match (o1, o2) with (Some v1, Some v2) then
      f v1 v2
    else
      d ()

utest optionZipWithOrElse (lam. "ERROR") (lam a. lam b. [a,b]) (Some 'm') (Some 'i') with "mi"
utest optionZipWithOrElse (lam. "ERROR") (lam a. lam b. [a,b]) (Some 'm') (None ()) with "ERROR"
utest optionZipWithOrElse (lam. "ERROR") (lam a. lam b. [a,b]) (None ()) (None ()) with "ERROR"

-- 'optionZipWithOr v f o1 o2' applies the function f on the values contained
-- in o1 and o2. If either o1 or o2 is None, then v is returned.
let optionZipWithOr: all a. all b. all c.
  c -> (a -> b -> c) -> (Option a) -> (Option b) -> c =
  lam v. optionZipWithOrElse (lam. v)

utest optionZipWithOr false eqi (Some 10) (Some 11) with false
utest optionZipWithOr false eqi (Some 10) (Some 10) with true
utest optionZipWithOr false eqi (Some 10) (None ()) with false
utest optionZipWithOr false eqi (None ()) (None ()) with false


-- Try to retrieve the contained value, or compute a default value
let optionGetOrElse: all a. (() -> a) -> Option a -> a = lam d. lam o.
  match o with Some t then
    t
  else
    d ()

utest optionGetOrElse (lam. 3) (Some 1) with 1
utest optionGetOrElse (lam. 3) (None ()) with 3

-- Try to retrieve the contained value, or fallback to a default value
let optionGetOr: all a. a -> Option a -> a = lam d.
  optionGetOrElse (lam. d)

utest optionGetOr 3 (Some 1) with 1
utest optionGetOr 3 (None ()) with 3

-- Applies a function to the contained value (if any),
-- or computes a default (if not).
let optionMapOrElse: all a. all b. (() -> b) -> (a -> b) -> Option a -> b =
  lam d. lam f. lam o.
  optionGetOrElse d (optionMap f o)

utest optionMapOrElse (lam. 3) (addi 1) (Some 1) with 2
utest optionMapOrElse (lam. 3) (addi 1) (None ()) with 3

-- Applies a function to the contained value (if any),
-- or returns the provided default (if not).
let optionMapOr: all a. all b. b -> (a -> b) -> Option a -> b =
  lam d. lam f. lam o.
  optionGetOr d (optionMap f o)

utest optionMapOr 3 (addi 1) (Some 1) with 2
utest optionMapOr 3 (addi 1) (None ()) with 3

-- 'optionMapM f l' maps each element of 'l' to an option using 'f'.
-- Then it collects the results to a new list option, which is 'Some'
-- only if all elements of 'l' were mapped to 'Some' by 'f'.
let optionMapM: all a. all b. (a -> Option b) -> [a] -> Option [b] = lam f. lam l.
  recursive let g = lam l. lam acc.
    match l with [hd] ++ rest then
      match f hd with Some x then
        g rest (snoc acc x)
      else
        None ()
    else
      Some acc
  in
  g l []

utest optionMapM (lam x. if gti x 2 then Some x else None ()) [3, 4, 5] with Some [3, 4, 5]
utest optionMapM (lam x. if gti x 2 then Some x else None ()) [2, 3, 4] with None ()

-- 'optionFoldlM f acc list' folds over 'list' using 'f', starting with the value 'acc'.
-- This is foldlM in the Option monad, i.e., if 'f' returns 'None' at any point the entire
-- result is 'None'.
let optionFoldlM: all a. all b. (a -> b -> Option a) -> a -> [b] -> Option a = lam f.
  recursive let recur = lam a. lam bs.
    match bs with [b] ++ bs then
      let res = f a b in
      match res with Some a then
        recur a bs
      else match res with None () then
        None ()
      else never
    else match bs with [] then
      Some a
    else never
  in recur

utest optionFoldlM (lam a. lam b. if gti (addi a b) 3 then None () else Some (addi a b)) 0 [1, 2]
      with Some 3 using optionEq eqi
utest optionFoldlM (lam a. lam b. if gti (addi a b) 3 then None () else Some (addi a b)) 0 [1, 2, 3]
      with None () using optionEq eqi
utest optionFoldlM (lam acc. lam x. Some (addi acc x)) 0 [1,2,3,4] with Some 10 using optionEq eqi
utest optionFoldlM (lam acc. lam x. if gti x acc then Some x else None ())
        0 [1,2,3,4]
with Some 4
using optionEq eqi
utest optionFoldlM (lam acc. lam x. if gti x acc then Some x else None ())
        0 [1,2,2,4]
with None ()
using optionEq eqi

-- Returns `true` if the option contains a value which
-- satisfies the specified predicate.
let optionContains: all a. Option a -> (a -> Bool) -> Bool = lam o. lam p.
  optionMapOr false p o

utest optionContains (Some 1) (eqi 1) with true
utest optionContains (Some 2) (eqi 1) with false
utest optionContains (None ()) (eqi 1) with false

-- Returns `true` if the option is a `Some` value.
let optionIsSome: all a. Option a -> Bool = lam o. optionContains o (lam. true)

utest optionIsSome (Some 1) with true
utest optionIsSome (None ()) with false

-- Returns `true` if the option is a `None` value.
let optionIsNone: all a. Option a -> Bool = lam o. not (optionIsSome o)

utest optionIsNone (None ()) with true
utest optionIsNone (Some 1) with false

-- Returns `None` if either option is `None`, otherwise returns
-- the first option.
let optionAnd: all a. Option a -> Option a -> Option a = lam o1. lam o2.
  match (o1, o2) with (Some _, Some _) then
    o1
  else
    None ()

utest optionAnd (Some 1) (Some 2) with (Some 1) using optionEq eqi
utest optionAnd (Some 1) (None ()) with (None ()) using optionEq eqi
utest optionAnd (None ()) (Some 1) with (None ()) using optionEq eqi
utest optionAnd (None ()) (None ()) with (None ()) using optionEq eqi

-- Filters the contained value (if any) using the specified predicate.
let optionFilter: all a. (a -> Bool) -> Option a -> Option a = lam p. lam o.
    if optionContains o p then
      o
    else
      None ()

utest optionFilter (eqi 1) (Some 1) with (Some 1) using optionEq eqi
utest optionFilter (eqi 2) (Some 1) with (None ()) using optionEq eqi
utest optionFilter (eqi 2) (None ()) with (None ()) using optionEq eqi

-- Returns the option if it contains a value, otherwise calls the specified
-- function and returns the result.
let optionOrElse: all a. (() -> Option a) -> Option a -> Option a = lam f. lam o.
  optionGetOrElse f (optionMap (lam x. Some x) o)

utest optionOrElse (lam. Some 2) (Some 1) with (Some 1) using optionEq eqi
utest optionOrElse (lam. Some 2) (None ()) with (Some 2) using optionEq eqi

-- Returns the first option if it contains a value, otherwise returns
-- the second option.
let optionOr: all a. Option a -> Option a -> Option a = lam o1. lam o2.
  optionOrElse (lam. o2) o1

utest optionOr (Some 1) (Some 2) with (Some 1) using optionEq eqi
utest optionOr (Some 1) (None ()) with (Some 1) using optionEq eqi
utest optionOr (None ()) (Some 2) with (Some 2) using optionEq eqi
utest optionOr (None ()) (None ()) with (None ()) using optionEq eqi

-- If exactly one option is `Some`, that option is returned,
-- otherwise returns `None`.
let optionXor: all a. Option a -> Option a -> Option a = lam o1. lam o2.
  match (o1, o2) with (Some _, None ()) then
    o1
  else match (o1, o2) with (None (), Some _) then
    o2
  else
    None ()

utest optionXor (Some 1) (Some 2) with (None ()) using optionEq eqi
utest optionXor (Some 1) (None ()) with (Some 1) using optionEq eqi
utest optionXor (None ()) (Some 2) with (Some 2) using optionEq eqi
utest optionXor (None ()) (None ()) with (None ()) using optionEq eqi
