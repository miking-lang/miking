-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The library defines the Either type and its two constructors: Left & Right.

include "option.mc"
include "seq.mc"

type Either a b
con Left: a -> Either a b
con Right: b -> Either a b


let eitherEq: (a -> c -> Bool) -> (b -> d -> Bool) -> Either a b -> Either c d -> Bool =
  lam eql. lam eqr. lam e1. lam e2.
  match (e1,e2) with (Left c1, Left c2) then
    eql c1 c2
  else match (e1,e2) with (Right c1, Right c2) then
    eqr c1 c2
  else
    false

utest eitherEq eqi eqi (Left 100) (Left 100) with true
utest eitherEq eqi eqi (Left 100) (Left 33) with false
utest eitherEq eqi eqi (Left 100) (Right 100) with false
utest eitherEq eqi eqi (Right 4321) (Right 4321) with true
utest eitherEq eqi eqi (Right 4321) (Right 1) with false
utest eitherEq eqi eqi (Right 4321) (Left 4321) with false


let eitherEither: (a -> c) -> (b -> c) -> Either a b -> c =
  lam lf. lam rf. lam e.
  match e with Left content then
    lf content
  else match e with Right content then
    rf content
  else never

utest eitherEither (eqi 1) (eqf 0.5) (Left 2) with false
utest eitherEither (eqi 1) (eqf 0.5) (Right 0.5) with true


let eitherBiMap: (a -> c) -> (b -> d) -> Either a b -> Either c d =
  lam lf. lam rf. lam e.
  match e with Left content then
    Left (lf content)
  else match e with Right content then
    Right (rf content)
  else never

utest eitherBiMap (addi 1) (cons 'a') (Left 2) with Left 3
utest eitherBiMap (addi 1) (cons 'a') (Right "choo") with Right "achoo"


let eitherMapLeft: (a -> c) -> Either a b -> Either c b = lam f. eitherBiMap f (lam x. x)

utest eitherMapLeft (cons 'a') (Right 5) with Right 5
utest eitherMapLeft (cons 'a') (Left "choo") with Left "achoo"


let eitherMapRight: (b -> c) -> Either a b -> Either a c = lam f. eitherBiMap (lam x. x) f

utest eitherMapRight (addi 2) (Right 40) with Right 42
utest eitherMapRight (addi 2) (Left "foo") with Left "foo"


let eitherBindLeft: Either a b -> (a -> Either c b) -> Either c b =
  lam e. lam bf.
  match e with Left content then
    bf content
  else match e with Right content then
    Right content
  else never

utest eitherBindLeft (Left "a") (lam s. Left (head s)) with Left 'a'
utest eitherBindLeft (Left "a") (lam _. Right 42) with Right 42
utest eitherBindLeft (Right 42) (lam s. Left (head s)) with Right 42


let eitherBindRight: Either a b -> (b -> Either a c) -> Either a c =
  lam e. lam bf.
  match e with Left content then
    Left content
  else match e with Right content then
    bf content
  else never

utest eitherBindRight (Left "a") (lam i. Right [int2char i]) with Left "a"
utest eitherBindRight (Right 10) (lam i. Right [int2char i]) with Right "\n"
utest eitherBindRight (Right 11) (lam _. Left "c") with Left "c"


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
