-- A simple library that defines map operations over sequences of tuples.

include "option.mc"
include "set.mc"

-- True if seq represents a map with equality defined by eq. Otherwise false.
let mapIsMap = lam eq. lam seq.
  setIsSet (lam x1. lam x2. eq x1.0 x2.0) seq

-- Optional value binded to k in seq, if no such binding in seq then None,
-- where equality defined by eq.
let mapLookupOpt = lam eq. lam k. lam seq. findAssoc (eq k) seq

-- Value binded to k in seq, if no such binding in seq then an error occurs.
-- Equality defined by eq.
let mapLookup = lam eq. lam k. lam seq.
  optionMapOrElse (mapLookupOpt eq k seq)
                  (lam _. error "Element not found")
                  (lam x. x)

-- True if k is bound in seq, else false.
-- Equality defined by eq.
let mapMem = lam eq. lam k. lam seq.
  optionIsSome (mapLookupOpt eq k seq)

-- Binds v to k in seq, where equality defined by eq.
let mapInsert = lam eq. lam k. lam v. lam seq.
  optionMapOrElse (index ( lam t. eq k t.0) seq)
                  (lam _. cons (k,v) seq)
                  (lam i. set seq i (k,v))

-- Updates seq by applying f to the value bound by k.
-- Equality defined by eq.
recursive
let mapUpdate = lam eq. lam k. lam f. lam seq.
  if null seq then seq
  else
    let x = head seq in
    let xs = tail seq in
    if eq k x.0 then
      cons (k, f x.1) xs
    else
      cons x (mapUpdate eq k f xs)
end

mexpr

let lookupOpt = mapLookupOpt eqi in
let lookup = mapLookup eqi in
let insert = mapInsert eqi in
let update = mapUpdate eqi in
let mem = mapMem eqi in

let m = [(1,'1'),(2,'2'),(3,'3')] in
let s = snoc m (1, '1') in

utest mapIsMap eqi m with true in
utest mapIsMap eqi s with false in

utest lookupOpt 1 m with Some '1' in
utest lookupOpt 2 m with Some '2' in
utest lookupOpt 3 m with Some '3' in
utest lookupOpt 4 m with None () in

let m = insert 1 '2' m in
let m = insert 2 '3' m in
let m = insert 3 '4' m in
let m = insert 4 '5' m in

utest lookupOpt 1 m with Some '2' in
utest lookupOpt 2 m with Some '3' in
utest lookupOpt 3 m with Some '4' in
utest lookupOpt 4 m with Some '5' in

let m = [(1,3), (4,6)] in
let m = update 1 (addi 2) m in
let m = update 4 (addi 1) m in
let m = update 5 (addi 3) m in

utest lookup 1 m with 5 in
utest lookup 4 m with 7 in

utest update 1 (lam _. error "Don't call me!") [] with [] in

utest mem 1 m with true in
utest mem 2 m with false in
utest mem 3 m with false in
utest mem 4 m with true in

()
