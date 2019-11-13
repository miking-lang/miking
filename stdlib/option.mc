type Option

con Some : Dyn -> Option
con None : () -> Option

-- Returns `true` if the option is a `Some` value.
let optionIsSome: Option -> Bool = lam o.
  match o with Some _ then
    true
  else
    false

-- Returns `true` if the option is a `None` value.
let optionIsNone: Option -> Bool = lam o.
  match o with None () then
    true
  else
    false

-- Returns `true` if the option contains a value which
-- satisfies the specified predicate.
let optionContains: Option -> (a -> Bool) -> Bool = lam o. lam p.
  match o with Some t then
    p t
  else
    false

-- Applies a function to the contained value (if any).
let optionMap: Option -> (a -> a) -> Option = lam o. lam f.
  match o with Some t then
    Some(f t)
  else
    None ()
    
-- Applies a function to the contained value (if any),
-- or returns the provided default (if not).
let optionMapOr: Option -> a -> (a -> a) -> a = lam o. lam d. lam f.
  match o with Some t then
    f t
  else
    d

-- Applies a function to the contained value (if any),
-- or computes a default (if not).
let optionMapOrElse: Option -> (Unit -> a) -> (a -> a) -> a = lam o. lam d. lam f.
  match o with Some t then
    f t
  else
    d unit

-- Returns `None` if either option is `None`, otherwise returns
-- the first option.
let optionAnd: Option -> Option -> Option = lam o1. lam o2.
  match o1 with Some _ then
    match o2 with Some _ then
      o1
    else
      None ()
  else
    None ()

-- Returns `None` if the option is `None`, otherwise calls the
-- specified function on the wrapped value and returns the result.
let optionFlatMap: Option -> (a -> Option) -> Option = lam o. lam f.
  match o with Some t then
    f t
  else
    None ()

-- Filters the contained value (if any) using the specified predicate.
let optionFilter: Option -> (a -> a) -> Option = lam o. lam p.
  match o with Some t then
    if p t then
      o
    else
      None ()
  else
    None ()
 
-- Returns the first option if it contains a value, otherwise returns
-- the second option.
let optionOr: Option -> Option -> Option = lam o1. lam o2.
  match o1 with Some _ then
    o1
  else
    o2
  
-- Returns the option if it contains a value, otherwise calls the specified
-- function and returns the result.
let optionOrElse: Option -> (Unit -> Option) -> Option = lam o. lam f.
  match o with Some _ then
    o
  else
    f unit

-- If exactly one option is `Some`, that option is returned,
-- otherwise returns `None`.
let optionXor: Option -> Option -> Option = lam o1. lam o2.
  match o1 with Some _ then
    match o2 with None () then
      o1
    else
      None ()
  else match o1 with None () then
    match o2 with Some _ then
      o2
    else
      None ()
  else
    None ()

-- Converts from `Option<Option<T>>` to `Option<T>`
let optionFlatten: Option -> Option = lam o.
  match o with Some t then
    t
  else
    None ()

mexpr

  utest optionIsNone (None ()) with true in
  utest optionIsNone (Some 1) with false in

  utest optionIsSome (Some 1) with true in
  utest optionIsSome (None ()) with false in

  utest optionContains (Some 1) (lam t. eqi t 1) with true in
  utest optionContains (Some 2) (lam t. eqi t 1) with false in
  utest optionContains (None ()) (lam t. eqi t 1) with false in

  utest optionMap (None ()) (lam t. addi t 1) with (None ()) in
  utest optionMap (Some 1) (lam t. addi t 1) with (Some 2) in

  utest optionFlatMap (None ()) (lam t. Some (addi t 1)) with (None ()) in
  utest optionFlatMap (Some 1) (lam t. Some (addi t 1)) with (Some 2) in
  utest optionFlatMap (Some 1) (lam t. None ()) with (None ()) in

  utest optionMapOr (Some 1) 3 (lam t. addi t 1) with 2 in
  utest optionMapOr (None ()) 3 (lam t. addi t 1) with 3 in

  utest optionMapOrElse (Some 1) (lam _. 3) (lam t. addi t 1) with 2 in
  utest optionMapOrElse (None ()) (lam _. 3) (lam t. addi t 1) with 3 in

  utest optionAnd (Some 1) (Some 2) with (Some 1) in
  utest optionAnd (Some 1) (None ()) with (None ()) in
  utest optionAnd (None ()) (Some 1) with (None ()) in
  utest optionAnd (None ()) (None ()) with (None ()) in

  utest optionFilter (Some 1) (lam t. eqi t 1) with (Some 1) in
  utest optionFilter (Some 1) (lam t. eqi t 2) with (None ()) in
  utest optionFilter (None ()) (lam t. eqi t 2) with (None ()) in

  utest optionOr (Some 1) (Some 2) with (Some 1) in
  utest optionOr (Some 1) (None ()) with (Some 1) in
  utest optionOr (None ()) (Some 2) with (Some 2) in
  utest optionOr (None ()) (None ()) with (None ()) in

  utest optionOrElse (Some 1) (lam _. Some 2) with (Some 1) in
  utest optionOrElse (None ()) (lam _. Some 2) with (Some 2) in

  utest optionXor (Some 1) (Some 2) with (None ()) in
  utest optionXor (Some 1) (None ()) with (Some 1) in
  utest optionXor (None ()) (Some 2) with (Some 2) in
  utest optionXor (None ()) (None ()) with (None ()) in

  utest optionFlatten (Some (Some 1)) with (Some 1) in
  utest optionFlatten (Some (None ())) with (None ()) in
  utest optionFlatten (None ()) with (None ()) in

  ()
