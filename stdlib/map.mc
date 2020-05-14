-- A simple library that defines map operations over sequences of tuples.

include "set.mc"

-- True if seq represents a map with equality defined by eq. Otherwise false.
let mapIsMap = lam eq. lam seq.
  setIsSet (lam x1. lam x2. eq x1.0 x2.0) seq

-- Optional value binded to k in seq, if no such binding in seq then None,
-- where equality defined by eq.
let mapFind = lam eq. lam k. lam seq. findAssoc (eq k) seq

-- Binds v to k in, seq where equality defined by eq.
let mapAdd = lam eq. lam k. lam v. lam seq.
  optionMapOrElse (index ( lam t. eq k t.0) seq)
                  (lam _. cons (k,v) seq)
                  (lam i. set seq i (k,v))

mexpr

let find = mapFind eqi in
let add = mapAdd eqi in

let m = [(1,'1'),(2,'2'),(3,'3')] in
let s = snoc m (1, '1') in

utest mapIsMap eqi m with true in
utest mapIsMap eqi s with false in

utest find 1 m with Some '1' in
utest find 2 m with Some '2' in
utest find 3 m with Some '3' in
utest find 4 m with None () in

let m = add 1 '2' m in
let m = add 2 '3' m in
let m = add 3 '4' m in
let m = add 4 '5' m in

utest find 1 m with Some '2' in
utest find 2 m with Some '3' in
utest find 3 m with Some '4' in
utest find 4 m with Some '5' in

()
