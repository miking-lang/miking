-- A simple library that defines set operations over sequences.

include "seq.mc"

-- True if seq represents a set with equality defined by eq. Otherwise false.
let setIsSet = lam eq. lam seq.
  eqi (length (distinct eq seq)) (length seq)

-- True if x is a member of seq, where equality is defined by eq. Otherwise
-- false.
let setMem = lam eq. lam x. lam seq.
  any (eq x) seq

-- True if the seq1 and seq2 are of the same length and contains the same
-- elements as defined by eq. Otherwise false.
let setEqual = lam eq. lam seq1. lam seq2.
  if neqi (length seq1) (length seq2) then false
  else all (lam x. setMem eq x seq2) seq1

-- The elements of seq1 that are not in seq2, where equality is defined by eq.
let setDiff = lam eq. lam seq1. lam seq2.
  filter (lam x1. not (setMem eq x1 seq2)) seq1

-- Inserts element x into seq if x not already in seq,
-- where equality is defined by eq.
let setInsert = lam eq. lam x. lam seq.
  if setMem eq x seq then seq else snoc seq x

-- The union of seq1 and seq2, where equality is defined by eq.
let setUnion = lam eq. lam seq1. lam seq2.
  foldr (setInsert eq) seq1 seq2

mexpr

let equal = setEqual eqi in
let diff = setDiff eqi in
let add = setInsert eqi in
let union = setUnion eqi in
let mem = setMem eqi in

utest setIsSet eqi [1,2,3] with true in
utest setIsSet eqi [1,2,3,2] with false in

utest equal [1,2] [1,2] with true in
utest equal [2,1] [1,2] with true in
utest equal [1,2] [1,2,3] with false in
utest equal [1,2,3] [1,2] with false in
utest equal [1,2] [1,3] with false in
utest equal [1,3] [1,2] with false in

utest equal (diff [1,2] [1,2]) [] with true in
utest equal (diff [1,2] [1,2,3]) [] with true in
utest equal (diff [1,2,3] [1,2]) [3] with true in
utest equal (diff [1,2] [1,3]) [2] with true in
utest equal (diff [1,3] [1,2]) [3] with true in

utest equal (add 1 [1,2]) [1,2] with true in
utest equal (add 2 [1,2]) [1,2] with true in
utest equal (add 3 [1,2]) [1,2,3] with true in

utest equal (union [1,2] [1,2]) [1,2] with true in
utest equal (union [1,2,3] [1,2]) [1,2,3] with true in
utest equal (union [1,2] [1,2,3]) [1,2,3] with true in
utest equal (union [1,2,3] [1,2,4]) [1,2,3,4] with true in

utest mem 1 [1,2] with true in
utest mem 2 [1,2] with true in
utest mem 3 [1,2] with false in

()
