type Option

con Some : Dyn -> Option
con None : () -> Option

-- Applies a function to the contained value (if any).
let optionMap: (a -> b) -> Option -> Option = lam f. lam o.
  match o with Some t then
    Some (f t)
  else
    None ()

-- Converts from `Option<Option<T>>` to `Option<T>`
let optionJoin: Option -> Option = lam o.
    match o with Some t then
      t
    else
      None ()

-- Returns `None` if the option is `None`, otherwise calls the
-- specified function on the wrapped value and returns the result.
let optionBind: Option -> (a -> Option) -> Option = lam o. lam f.
    optionJoin (optionMap f o)

-- Try to retrieve the contained value, or compute a default value
let optionGetOrElse: (Unit -> a) -> Option -> a = lam d. lam o.
  match o with Some t then
    t
  else
    d ()

-- Try to retrieve the contained value, or fallback to a default value
let optionGetOr: a -> Option -> a = lam d.
  optionGetOrElse (lam _. d)

-- Applies a function to the contained value (if any),
-- or computes a default (if not).
let optionMapOrElse: (Unit -> b) -> (a -> b) -> Option -> b = lam d. lam f. lam o.
  optionGetOrElse d (optionMap f o)

-- Applies a function to the contained value (if any),
-- or returns the provided default (if not).
let optionMapOr: b -> (a -> b) -> Option -> b = lam d. lam f. lam o.
  optionGetOr d (optionMap f o)

-- Returns `true` if the option contains a value which
-- satisfies the specified predicate.
let optionContains: Option -> (a -> Bool) -> Bool = lam o. lam p.
  optionMapOr false p o

-- Returns `true` if the option is a `Some` value.
let optionIsSome: Option -> Bool = lam o. optionContains o (lam _. true)

-- Returns `true` if the option is a `None` value.
let optionIsNone: Option -> Bool = lam o. not (optionIsSome o)

-- Returns `None` if either option is `None`, otherwise returns
-- the first option.
let optionAnd: Option -> Option -> Option = lam o1. lam o2.
  match (o1, o2) with (Some _, Some _) then
    o1
  else
    None ()

-- Filters the contained value (if any) using the specified predicate.
let optionFilter: (a -> Bool) -> Option -> Option = lam p. lam o.
    if optionContains o p then
      o
    else
      None ()

-- Returns the option if it contains a value, otherwise calls the specified
-- function and returns the result.
let optionOrElse: (Unit -> Option) -> Option -> Option = lam f. lam o.
  optionGetOrElse f (optionMap Some o)

-- Returns the first option if it contains a value, otherwise returns
-- the second option.
let optionOr: Option -> Option -> Option = lam o1. lam o2.
  optionOrElse (lam _. o2) o1

-- If exactly one option is `Some`, that option is returned,
-- otherwise returns `None`.
let optionXor: Option -> Option -> Option = lam o1. lam o2.
  match (o1, o2) with (Some _, None ()) then
    o1
  else match (o1, o2) with (None (), Some _) then
    o2
  else
    None ()

mexpr

  utest optionMap (addi 1) (None ()) with (None ()) in
  utest optionMap (addi 1) (Some 1) with (Some 2) in

  utest optionJoin (Some (Some 1)) with (Some 1) in
  utest optionJoin (Some (None ())) with (None ()) in
  utest optionJoin (None ()) with (None ()) in

  utest optionBind (None ()) (lam t. Some (addi 1 t)) with (None ()) in
  utest optionBind (Some 1) (lam t. Some (addi 1 t)) with (Some 2) in
  utest optionBind (Some 1) (lam _. None ()) with (None ()) in

  utest optionGetOrElse (lam _. 3) (Some 1) with 1 in
  utest optionGetOrElse (lam _. 3) (None ()) with 3 in

  utest optionGetOr 3 (Some 1) with 1 in
  utest optionGetOr 3 (None ()) with 3 in

  utest optionMapOrElse (lam _. 3) (addi 1) (Some 1) with 2 in
  utest optionMapOrElse (lam _. 3) (addi 1) (None ()) with 3 in

  utest optionMapOr 3 (addi 1) (Some 1) with 2 in
  utest optionMapOr 3 (addi 1) (None ()) with 3 in

  utest optionContains (Some 1) (eqi 1) with true in
  utest optionContains (Some 2) (eqi 1) with false in
  utest optionContains (None ()) (eqi 1) with false in

  utest optionIsNone (None ()) with true in
  utest optionIsNone (Some 1) with false in

  utest optionIsSome (Some 1) with true in
  utest optionIsSome (None ()) with false in

  utest optionAnd (Some 1) (Some 2) with (Some 1) in
  utest optionAnd (Some 1) (None ()) with (None ()) in
  utest optionAnd (None ()) (Some 1) with (None ()) in
  utest optionAnd (None ()) (None ()) with (None ()) in

  utest optionFilter (eqi 1) (Some 1) with (Some 1) in
  utest optionFilter (eqi 2) (Some 1) with (None ()) in
  utest optionFilter (eqi 2) (None ()) with (None ()) in

  utest optionOr (Some 1) (Some 2) with (Some 1) in
  utest optionOr (Some 1) (None ()) with (Some 1) in
  utest optionOr (None ()) (Some 2) with (Some 2) in
  utest optionOr (None ()) (None ()) with (None ()) in

  utest optionOrElse (lam _. Some 2) (Some 1) with (Some 1) in
  utest optionOrElse (lam _. Some 2) (None ()) with (Some 2) in

  utest optionXor (Some 1) (Some 2) with (None ()) in
  utest optionXor (Some 1) (None ()) with (Some 1) in
  utest optionXor (None ()) (Some 2) with (Some 2) in
  utest optionXor (None ()) (None ()) with (None ()) in

  ()
