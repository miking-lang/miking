
include "option.mc"
include "seq.mc"

-- Implements an iterator for traversing (in-)finite sequences.

type Iterator a b =
{ state : Option a
, step : Option a -> Option a
, getVal : a -> b
}

-- 'iteratorInit step get' returns an iterator with step function 'step' and get
-- function 'get'.
let iteratorInit
  : all a. all b.
     (Option a -> Option a)
  -> (a -> b)
  -> Iterator a b
  = lam step. lam getVal.
    {state = None (), step = step, getVal = getVal}

-- 'iteratorStep' moves the iterator one step and returns the new iterator.
let iteratorStep : all a. all b. Iterator a b -> Iterator a b = lam it.
  match it with {state = state, step = step} then
    {it with state = step state}
  else never

-- 'iteratorGet it' returns the current value of the iterator.
let iteratorGet : all a. all b. Iterator a b -> Option b = lam it.
  match it with {state = state, getVal = getVal} then
    match state with Some v then Some (getVal v)
    else None ()
  else never

-- 'iteratorNext it' moves the iterator one step. Returns both the new iterator
-- and the current value.
let iteratorNext : all a. all b. Iterator a b -> (Iterator a b, Option b) = lam it.
  let it = iteratorStep it in
  (it, iteratorGet it)

-- 'iteratorToSeq it' converts 'it' into a sequence.
let iteratorToSeq : all a. all b. Iterator a b -> [b] = lam it.
  recursive let work = lam acc. lam it.
    let n = iteratorNext it in
    match n with (_, None ()) then acc
    else match n with (it, Some v) then
      work (cons v acc) it
    else never
  in reverse (work [] it)

-- 'iteratorFromSeq seq' converts 'seq' into an iterator.
let iteratorFromSeq : all a. [a] -> Iterator [a] a = lam seq.
  let step = lam state.
    match state with Some ([] | [_]) then None ()
    else match state with Some seq then Some (tail seq)
    else match seq with [] then None ()
    else Some seq
  in
  let getVal = lam seq. head seq in
  iteratorInit step getVal

-- 'iteratorTake n it' returns at most the first 'n' elements in iterator 'it'.
-- If 'n' is negative, or if 'n' is larger than the number of elements in 'it',
-- then all elements in 'it' are returned.
let iteratorTake : all a. all b. Int -> Iterator a b -> [b] = lam n. lam it.
  recursive let work = lam acc. lam n. lam it.
    if eqi n 0 then acc
    else
      let nx = iteratorNext it in
      match nx with (_, None ()) then acc
      else match nx with (it, Some v) then
        work (cons v acc) (subi n 1) it
      else never
  in reverse (work [] n it)

-- 'iteratorFilter p it' returns a new iterator containing those element in 'it'
-- that satisfy 'p'.
let iteratorFilter : all a. all b. (b -> Bool) -> Iterator a b -> Iterator a b =
  lam p. lam it.
    {it with step = lam state.
       recursive let step = lam state.
         match it.step state with Some state then
           if p (it.getVal state) then Some state
           else step (Some state)
         else None ()
       in step state}

-- 'iteratorRange min max' returns a new iterator over the values in the range
-- 'min', 'min' + 1, ..., 'max'
let iteratorRange : Int -> Int -> Iterator Int Int =
  lam min. lam max.
    iteratorInit (lam v.
      match v with Some v then
        if lti v max then Some (addi v 1)
        else None ()
      else Some min)
      (lam x. x)

mexpr
let next = iteratorNext in

let it = iteratorRange 1 3 in

utest (next it).1 with Some 1 using optionEq eqi in
utest (next (next it).0).1 with Some 2 using optionEq eqi in
utest (next (next (next it).0).0).1 with Some 3 using optionEq eqi in
utest (next (next (next (next it).0).0).0).1 with None () using optionEq eqi in

utest iteratorGet it with None () using optionEq eqi in
utest iteratorGet (next it).0 with Some 1 using optionEq eqi in

utest iteratorToSeq it with [1,2,3] in

utest iteratorToSeq (iteratorFromSeq []) with [] using eqSeq eqi in
utest iteratorToSeq (iteratorFromSeq [1]) with [1] in
utest iteratorToSeq (iteratorFromSeq [1,2,3]) with [1,2,3] in

utest iteratorTake 0 it with [] using eqSeq eqi in
utest iteratorTake 2 it with [1,2] in
utest iteratorTake 100 it with [1,2,3] in
utest iteratorTake (subi 0 1) it with [1,2,3] in

utest iteratorToSeq (iteratorFilter (leqi 3) (iteratorFromSeq [1,3,8,subi 0 1]))
with [3, 8] in

()
