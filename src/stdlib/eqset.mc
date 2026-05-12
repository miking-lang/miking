-- A simple library that defines set operations over sequences. Multiple
-- occurances of an element, according to a provided equality function, in a
-- sequence is considered a single element in the set. The time complexity of
-- these operations are typically worse compared to `set.mc` so this library is
-- mostly suitable for sets with small cardinality.

include "common.mc"
include "seq.mc"

-- `true` if `x` is a member of `xs`, where equality is defined by `eq`,
-- otherwise `false`.
let eqsetMem : all a. all b. (a -> b -> Bool) -> a -> [b] -> Bool =
  lam eq. lam x. lam xs.
    any (eq x) xs

utest eqsetMem eqi 1 [1,2,2] with true
utest eqsetMem eqi 2 [1,2,2] with true
utest eqsetMem eqi 3 [1,2,2] with false

-- The cardinality of the set `xs`, as defined by `eq`.
let eqsetCardinality : all a. (a -> a -> Bool) -> [a] -> Int =
  lam eq. lam xs.
    length (distinct eq xs)

utest eqsetCardinality eqi [] with 0
utest eqsetCardinality eqi [1,1,2] with 2
utest eqsetCardinality eqi [1,1,3,2,1] with 3

-- `true` if the elements of `xs` are in `ys` as defined by `eq`, otherwise
-- `false`.
let eqsetIsSubsetEq : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> Bool =
  lam eq. lam xs. lam ys. forAll (lam x. eqsetMem eq x ys) xs

utest eqsetIsSubsetEq eqi [1,2] [1,2,1] with true
utest eqsetIsSubsetEq eqi [2,1,2] [1,2] with true
utest eqsetIsSubsetEq eqi [1,2] [1,2,3] with true
utest eqsetIsSubsetEq eqi [1,2,3] [1,2] with false
utest eqsetIsSubsetEq eqi [1,2] [1,3] with false
utest eqsetIsSubsetEq eqi [1,3,1] [1,2,2] with false

-- `true` if `xs` and `ys` are of the same length and contains the same elements
-- as defined by `eq`, otherwise `false`.
let eqsetEqual : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> Bool =
  lam eq. lam xs. lam ys.
    and (eqsetIsSubsetEq eq xs ys) (eqsetIsSubsetEq (flip eq) ys xs)

utest eqsetEqual eqi [1,2] [1,2] with true
utest eqsetEqual eqi [2,1] [1,2,1] with true
utest eqsetEqual eqi [1,2,2] [1,2,3] with false
utest eqsetEqual eqi [1,2,3] [1,2] with false
utest eqsetEqual eqi [1,2] [1,3] with false
utest eqsetEqual eqi [1,3] [1,2] with false

-- The elements of `xs` that are not in `ys`, where equality is defined by `eq`.
let eqsetDiff : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> [a] =
  lam eq. lam xs. lam ys.
    filter (lam x. not (eqsetMem eq x ys)) xs

utest eqsetEqual eqi (eqsetDiff eqi [1,2,2] [1,2]) [] with true
utest eqsetEqual eqi (eqsetDiff eqi [1,1,2] [1,2,3,3]) [] with true
utest eqsetEqual eqi (eqsetDiff eqi [1,2,3] [1,2]) [3] with true
utest eqsetEqual eqi (eqsetDiff eqi [1,2,1] [3,1,3]) [2] with true
utest eqsetEqual eqi (eqsetDiff eqi [1,3] [1,2]) [3] with true

-- Inserts element `x` into `xs` if `x` not already in `xs`, where equality is
-- defined by `eq`.
let eqsetInsert : all a. (a -> a -> Bool) -> a -> [a] -> [a] =
  lam eq. lam x. lam xs.
    if eqsetMem eq x xs then xs else snoc xs x

utest eqsetEqual eqi (eqsetInsert eqi 1 [1,2]) [1,2] with true
utest eqsetEqual eqi (eqsetInsert eqi 2 [1,2]) [1,2] with true
utest eqsetEqual eqi (eqsetInsert eqi 3 [1,2,2]) [1,2,3] with true

-- The union of `xs` and `ys`, where equality is defined by `eq`.
let eqsetUnion : all a. (a -> a -> Bool) -> [a] -> [a] -> [a] =
  lam eq. lam xs. lam ys.
    foldr (eqsetInsert eq) xs ys

utest eqsetEqual eqi (eqsetUnion eqi [1,2] [1,2]) [1,2] with true
utest eqsetEqual eqi (eqsetUnion eqi [1,2,3] [1,2]) [1,2,3] with true
utest eqsetEqual eqi (eqsetUnion eqi [1,2] [1,2,3]) [1,2,3] with true
utest eqsetEqual eqi (eqsetUnion eqi [1,2,3] [1,2,2,4]) [1,2,3,4] with true

-- The elements of `xs` that are in `ys`, where equality is defined by `eq`.
let eqsetIntersection : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> [a] =
  lam eq. lam xs. lam ys.
    filter (lam x. eqsetMem eq x ys) xs

utest eqsetEqual eqi (eqsetIntersection eqi [1,2] [1,2]) [1,2] with true
utest eqsetEqual eqi (eqsetIntersection eqi [1,2,3,3] [1,2,1]) [1,2] with true
utest eqsetEqual eqi (eqsetIntersection eqi [1,2] [1,2,3]) [1,2] with true
utest eqsetEqual eqi (eqsetIntersection eqi [1,2,3] [1,2,4,4]) [1,2] with true
