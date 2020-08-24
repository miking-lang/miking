type Option

con Some : Dyn -> Option
con None : () -> Option

-- Applies a function to the contained value (if any).
let optionMap: (a -> b) -> Option -> Option = lam f. lam o.
  match o with Some t then
    Some (f t)
  else
    None ()

utest optionMap (addi 1) (None ()) with (None ())
utest optionMap (addi 1) (Some 1) with (Some 2)

-- Converts from `Option<Option<T>>` to `Option<T>`
let optionJoin: Option -> Option = lam o.
    match o with Some t then
      t
    else
      None ()

utest optionJoin (Some (Some 1)) with (Some 1)
utest optionJoin (Some (None ())) with (None ())
utest optionJoin (None ()) with (None ())

-- Returns `None` if the option is `None`, otherwise calls the
-- specified function on the wrapped value and returns the result.
let optionBind: Option -> (a -> Option) -> Option = lam o. lam f.
    optionJoin (optionMap f o)

utest optionBind (None ()) (lam t. Some (addi 1 t)) with (None ())
utest optionBind (Some 1) (lam t. Some (addi 1 t)) with (Some 2)
utest optionBind (Some 1) (lam _. None ()) with (None ())

-- 'optionCompose f g' composes the option-producing functions f and g into
-- a new function, which only succeeds if both f and g succeed.
let optionCompose: (b -> Option) -> (a -> Option) -> a -> Option =
  lam f. lam g. lam x.
    optionBind (g x) f

utest optionCompose (lam t. Some (addi 1 t)) (lam t. Some (muli 2 t)) 2 with Some 5
utest optionCompose (lam t. None ()) (lam t. Some (muli 2 t)) 2 with None ()
utest optionCompose (lam t. Some (addi 1 t)) (lam t. None ()) 2 with None ()

-- Try to retrieve the contained value, or compute a default value
let optionGetOrElse: (Unit -> a) -> Option -> a = lam d. lam o.
  match o with Some t then
    t
  else
    d ()

utest optionGetOrElse (lam _. 3) (Some 1) with 1
utest optionGetOrElse (lam _. 3) (None ()) with 3

-- Try to retrieve the contained value, or fallback to a default value
let optionGetOr: a -> Option -> a = lam d.
  optionGetOrElse (lam _. d)

utest optionGetOr 3 (Some 1) with 1
utest optionGetOr 3 (None ()) with 3

-- Applies a function to the contained value (if any),
-- or computes a default (if not).
let optionMapOrElse: (Unit -> b) -> (a -> b) -> Option -> b = lam d. lam f. lam o.
  optionGetOrElse d (optionMap f o)

utest optionMapOrElse (lam _. 3) (addi 1) (Some 1) with 2
utest optionMapOrElse (lam _. 3) (addi 1) (None ()) with 3

-- Applies a function to the contained value (if any),
-- or returns the provided default (if not).
let optionMapOr: b -> (a -> b) -> Option -> b = lam d. lam f. lam o.
  optionGetOr d (optionMap f o)

utest optionMapOr 3 (addi 1) (Some 1) with 2
utest optionMapOr 3 (addi 1) (None ()) with 3

-- 'optionMapM f l' maps each element of 'l' to an option using 'f'.
-- Then it collects the results to a new list option, which is 'Some'
-- only if all elements of 'l' were mapped to 'Some' by 'f'.
let optionMapM: (a -> Option) -> [a] -> Option = lam f. lam l.
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

-- Returns `true` if the option contains a value which
-- satisfies the specified predicate.
let optionContains: Option -> (a -> Bool) -> Bool = lam o. lam p.
  optionMapOr false p o

utest optionContains (Some 1) (eqi 1) with true
utest optionContains (Some 2) (eqi 1) with false
utest optionContains (None ()) (eqi 1) with false

-- Returns `true` if the option is a `Some` value.
let optionIsSome: Option -> Bool = lam o. optionContains o (lam _. true)

utest optionIsSome (Some 1) with true
utest optionIsSome (None ()) with false

-- Returns `true` if the option is a `None` value.
let optionIsNone: Option -> Bool = lam o. not (optionIsSome o)

utest optionIsNone (None ()) with true
utest optionIsNone (Some 1) with false

-- Returns `None` if either option is `None`, otherwise returns
-- the first option.
let optionAnd: Option -> Option -> Option = lam o1. lam o2.
  match (o1, o2) with (Some _, Some _) then
    o1
  else
    None ()

utest optionAnd (Some 1) (Some 2) with (Some 1)
utest optionAnd (Some 1) (None ()) with (None ())
utest optionAnd (None ()) (Some 1) with (None ())
utest optionAnd (None ()) (None ()) with (None ())

-- Filters the contained value (if any) using the specified predicate.
let optionFilter: (a -> Bool) -> Option -> Option = lam p. lam o.
    if optionContains o p then
      o
    else
      None ()

utest optionFilter (eqi 1) (Some 1) with (Some 1)
utest optionFilter (eqi 2) (Some 1) with (None ())
utest optionFilter (eqi 2) (None ()) with (None ())

-- Returns the option if it contains a value, otherwise calls the specified
-- function and returns the result.
let optionOrElse: (Unit -> Option) -> Option -> Option = lam f. lam o.
  optionGetOrElse f (optionMap (lam x. Some x) o)

utest optionOrElse (lam _. Some 2) (Some 1) with (Some 1)
utest optionOrElse (lam _. Some 2) (None ()) with (Some 2)

-- Returns the first option if it contains a value, otherwise returns
-- the second option.
let optionOr: Option -> Option -> Option = lam o1. lam o2.
  optionOrElse (lam _. o2) o1

utest optionOr (Some 1) (Some 2) with (Some 1)
utest optionOr (Some 1) (None ()) with (Some 1)
utest optionOr (None ()) (Some 2) with (Some 2)
utest optionOr (None ()) (None ()) with (None ())

-- If exactly one option is `Some`, that option is returned,
-- otherwise returns `None`.
let optionXor: Option -> Option -> Option = lam o1. lam o2.
  match (o1, o2) with (Some _, None ()) then
    o1
  else match (o1, o2) with (None (), Some _) then
    o2
  else
    None ()

utest optionXor (Some 1) (Some 2) with (None ())
utest optionXor (Some 1) (None ()) with (Some 1)
utest optionXor (None ()) (Some 2) with (Some 2)
utest optionXor (None ()) (None ()) with (None ())
