
include "option.mc"
include "seq.mc"

type Iterator a b =
{ state : Option a
, step : Option a -> Option a
, getVal : a -> b
}

let iteratorInit :
   (Option a -> Option a) -> (Option a -> Option a) -> Iterator a b
  = lam step. lam getVal.
    {state = None (), step = step, getVal = getVal}

let iteratorStep : Iterator a b -> Iterator a b = lam it.
  match it with {state = state, step = step} then
    {it with state = step state}
  else never

let iteratorGet : Iterator a b -> Some b = lam it.
  match it with {state = state, getVal = getVal} then
    match state with Some v then Some (getVal v)
    else None ()
  else never

let iteratorNext : Iterator a b -> (Iterator a b, Option b) = lam it.
  let it = iteratorStep it in
  (it, iteratorGet it)

let iteratorToSeq : Iterator a b -> [b] = lam it.
  recursive let work = lam acc. lam it.
    let n = iteratorNext it in
    match n with (_, None ()) then acc
    else match n with (it, Some v) then
      work (cons v acc) it
    else never
  in reverse (work [] it)

let iteratorFromSeq : [a] -> Iterator [a] a = lam seq.
  let step = lam state.
    match state with Some ([] | [_]) then None ()
    else match state with Some seq then Some (tail seq)
    else match seq with [] then None ()
    else Some seq
  in
  let getVal = lam seq. head seq in
  iteratorInit step getVal

mexpr
let next = iteratorNext in

let it = iteratorInit (lam v.
  match v with Some v then
    if lti v 3 then Some (addi v 1)
    else None ()
  else Some 1) (lam x. x) in

utest (next it).1 with Some 1 using optionEq eqi in
utest (next (next it).0).1 with Some 2 using optionEq eqi in
utest (next (next (next it).0).0).1 with Some 3 using optionEq eqi in
utest (next (next (next (next it).0).0).0).1 with None () using optionEq eqi in

utest iteratorToSeq it with [1,2,3] in

utest iteratorToSeq (iteratorFromSeq []) with [] using eqSeq eqi in
utest iteratorToSeq (iteratorFromSeq [1]) with [1] in
utest iteratorToSeq (iteratorFromSeq [1,2,3]) with [1,2,3] in

()
