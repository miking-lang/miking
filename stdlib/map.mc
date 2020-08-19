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
  optionGetOrElse (lam _. error "Element not found")
                  (mapLookupOpt eq k seq)

-- True if k is bound in seq, else false.
-- Equality defined by eq.
let mapMem = lam eq. lam k. lam seq.
  optionIsSome (mapLookupOpt eq k seq)

-- Binds v to k in seq, where equality defined by eq.
let mapInsert = lam eq. lam k. lam v. lam seq.
  optionMapOrElse (lam _. cons (k,v) seq)
                  (lam i. set seq i (k,v))
                  (index (lam t. eq k t.0) seq)

-- Removes a key-value pair from the map, if it exists
let mapRemove = lam eq. lam key. lam seq.
  optionMapOr seq
              (lam i.
                let spl = splitAt seq i in
                concat spl.0 (tail spl.1))
              (index (lam t. eq key t.0) seq)
mexpr

let lookupOpt = mapLookupOpt eqi in
let lookup = mapLookup eqi in
let insert = mapInsert eqi in
let mem = mapMem eqi in
let remove = mapRemove eqi in

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

utest mem 1 m with true in
utest mem 2 m with false in
utest mem 3 m with false in
utest mem 4 m with true in

let m = remove 1 m in

utest mem 1 m with false in
utest mem 4 m with true in

let m = remove 1 m in
let m = remove 3 m in

utest mem 1 m with false in
utest mem 4 m with true in

let m = remove 4 m in

utest mem 4 m with false in

()
