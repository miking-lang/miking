-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The library defines the Either type and its two constructors: Left & Right.

include "option.mc"
include "seq.mc"

type Either a b
con Left: a -> Either a b
con Right: b -> Either a b


let eitherEither: (a -> c) -> (b -> c) -> Either a b -> c =
  lam lf. lam rf. lam e.
  match e with Left content then
    lf content
  else match e with Right content then
    rf content
  else never

utest eitherEither (eqi 1) (eqf 0.5) (Left 2) with false
utest eitherEither (eqi 1) (eqf 0.5) (Right 0.5) with true


let eitherPartition: [Either a b] -> ([a],[b]) = lam es.
  foldl (lam acc. lam e.
    match e with Left content then
      (snoc acc.0 content, acc.1)
    else match e with Right content then
      (acc.0, snoc acc.1 content)
    else never
  ) ([],[]) es

utest eitherPartition [] with ([], [])
utest eitherPartition [Left 1, Right "foo", Right "bar", Left 42] with ([1,42], ["foo", "bar"])
utest eitherPartition [Right 5.0, Right 1.0, Left "42"] with (["42"], [5.0, 1.0])


let eitherLefts: [Either a b] -> [a] = lam es. (eitherPartition es).0

utest eitherLefts [] with []
utest eitherLefts [Right 1, Right 5] with []
utest eitherLefts [Right 1, Left "c", Right 5, Left "a"] with ["c", "a"]


let eitherRights: [Either a b] -> [b] = lam es. (eitherPartition es).1

utest eitherRights [] with []
utest eitherRights [Left "1", Left "5"] with []
utest eitherRights [Right 1, Left "3", Right 5, Left "1"] with [1, 5]


let eitherIsLeft: Either a b -> Bool = lam e.
  match e with Left _ then true else false

utest eitherIsLeft (Left 5) with true
utest eitherIsLeft (Left "a") with true
utest eitherIsLeft (Right "a") with false
utest eitherIsLeft (Right (Left 1)) with false


let eitherIsRight: Either a b -> Bool = lam e.
  match e with Right _ then true else false

utest eitherIsRight (Left 5) with false
utest eitherIsRight (Left "a") with false
utest eitherIsRight (Right "a") with true
utest eitherIsRight (Right (Left 1)) with true


let eitherFromLeft: a -> Either a b -> a = lam v. lam e.
  match e with Left content then
    content
  else
    v

utest eitherFromLeft "a" (Right 5) with "a"
utest eitherFromLeft "a" (Left "foo") with "foo"


let eitherFromRight: b -> Either a b -> b = lam v. lam e.
  match e with Right content then
    content
  else
    v

utest eitherFromRight 0 (Left "foo") with 0
utest eitherFromRight 0 (Right 42) with 42


let eitherGetLeft: Either a b -> Option a = lam e.
  match e with Left content then
    Some content
  else
    None ()

utest eitherGetLeft (Left "foo") with Some "foo"
utest eitherGetLeft (Right 42) with None ()


let eitherGetRight: Either a b -> Option b = lam e.
  match e with Right content then
    Some content
  else
    None ()

utest eitherGetRight (Left "foo") with None ()
utest eitherGetRight (Right 42) with Some 42
