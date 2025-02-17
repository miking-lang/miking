-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- This library defines the Either type and its two constructors: Left & Right.

include "option.mc"
include "seq.mc"
include "string.mc"
include "basic-types.mc"

--  *-
--  * .brief Checks equality between two Either values.
--  *
--  * .lam[eql] Function that checks left equality
--  * .lam[eqr] Function that checks right equality
--  * .lam[e1] Either value to be compared
--  * .lam[e2] The other Either value to be compared
--  *
--  * .return Whether e1 and e2 are equal based on the provided equaliy
--  *         functions.
-- -*
let eitherEq: all a. all b. all c. all d.
  (a -> c -> Bool) -> (b -> d -> Bool) -> Either a b -> Either c d -> Bool =
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

--  *-
--  * .brief Case analysis of an Either type to extract its value.
--  *
--  * .lam[lf] How a Left value should be extracted
--  * .lam[rf] How a Right value should be extracted
--  * .lam[e] The Either value to have have its value extracted
--  *
--  * .return The value that was extracted from the case analysis.
-- -*
let eitherEither: all a. all b. all c. (a -> c) -> (b -> c) -> Either a b -> c =
  lam lf. lam rf. lam e.
  match e with Left content then
    lf content
  else match e with Right content then
    rf content
  else never

utest eitherEither (eqi 1) (eqf 0.5) (Left 2) with false
utest eitherEither (eqi 1) (eqf 0.5) (Right 0.5) with true

--  *-
--  * .brief Maps a function onto an either value, one function for each case.
--  *
--  * .lam[lf] The Left mapping function
--  * .lam[rf] The Right mapping function
--  * .lam[e] The Either value to map a function on
--  *
--  * .return The map result as an Either type, concealing which case that was
--  *         actually mapped on.
-- -*
let eitherBiMap: all a. all b. all c. all d.
  (a -> c) -> (b -> d) -> Either a b -> Either c d =
  lam lf. lam rf. lam e.
  match e with Left content then
    Left (lf content)
  else match e with Right content then
    Right (rf content)
  else never

utest eitherBiMap (addi 1) (cons 'a') (Left 2)
with Left 3 using eitherEq eqi eqString
utest eitherBiMap (addi 1) (cons 'a') (Right "choo")
with Right "achoo" using eitherEq eqi eqString

--  *-
--  * .brief Maps a function onto the Left value if that is the Either case.
--  *
--  * .lam[f] The mapping function
--  * .lam[e] The Either value to map a function on
--  *
--  * .return The map result as an Either type, in the Left case containing
--  *         the mapped value and in the Right case staying the same.
-- -*
let eitherMapLeft: all a. all b. all c.
  (a -> c) -> Either a b -> Either c b = lam f. eitherBiMap f (lam x. x)

utest eitherMapLeft (cons 'a') (Right 5) with Right 5 using eitherEq eqString eqi
utest eitherMapLeft (cons 'a') (Left "choo")
with Left "achoo" using eitherEq eqString eqi

--  *-
--  * .brief Maps a function onto the Right value if that is the Either case.
--  *
--  * .lam[f] The mapping function
--  * .lam[e] The Either value to map a function on
--  *
--  * .return The map result as an Either type, in the Right case containing
--  *         the mapped value and in the Left case staying the same.
-- -*
let eitherMapRight: all a. all b. all c.
  (b -> c) -> Either a b -> Either a c = lam f. eitherBiMap (lam x. x) f

utest eitherMapRight (addi 2) (Right 40) with Right 42 using eitherEq eqString eqi
utest eitherMapRight (addi 2) (Left "foo")
with Left "foo" using eitherEq eqString eqi

--  *-
--  * .brief If the input Either is the Left case, then its value is applied as
--  *        the argument to the passed function.
--  *
--  * .lam[e] The Either value whose Left case will be bound as input
--  * .lam[bf] The function to have the Left value applied to
--  *
--  * .return If the Either argument is a Left case, the result of binding its
--  *         value to the passed function. If it is the Right case, then it is
--  *         returned as is.
-- -*
let eitherBindLeft: all a. all b. all c. Either a b -> (a -> Either c b) -> Either c b =
  lam e. lam bf.
  match e with Left content then
    bf content
  else match e with Right content then
    Right content
  else never

utest eitherBindLeft (Left "a") (lam s. Left (head s))
with Left 'a' using eitherEq eqc eqi
utest eitherBindLeft (Left "a") (lam. Right 42)
with Right 42 using eitherEq eqString eqi
utest eitherBindLeft (Right 42) (lam s. Left (head s))
with Right 42 using eitherEq eqc eqi

--  *-
--  * .brief If the input Either is the Right case, then its value is applied
--  *        as the argument to the passed function.
--  *
--  * .lam[e] The Either value whose Right case will be bound as input
--  * .lam[bf] The function to have the Right value applied to
--  *
--  * .return If the Either argument is a Right case, the result of binding its
--  *         value to the passed function. If it is the Left case, then it is
--  *         returned as is.
-- -*
let eitherBindRight: all a. all b. all c.
  Either a b -> (b -> Either a c) -> Either a c =
  lam e. lam bf.
  match e with Left content then
    Left content
  else match e with Right content then
    bf content
  else never

utest eitherBindRight (Left "a") (lam i. Right [int2char i])
with Left "a" using eitherEq eqString eqString
utest eitherBindRight (Right 10) (lam i. Right [int2char i])
with Right "\n" using eitherEq eqString eqString
utest eitherBindRight (Right 11) (lam. Left "c")
with Left "c" using eitherEq eqString eqi

--  *-
--  * .brief Partitions a list of Eithers into the Left case values and the
--  *        Right case values.
--  *
--  * .lam[es] List of Either values to partition
--  *
--  * .return A tuple with the first element containing the Left values and the
--  *         second element containing the Right values, preserving order in
--  *         relation to the input list.
-- -*
let eitherPartition: all a. all b. [Either a b] -> ([a],[b]) = lam es.
  foldl (lam acc : ([a], [b]). lam e.
    match e with Left content then
      (snoc acc.0 content, acc.1)
    else match e with Right content then
      (acc.0, snoc acc.1 content)
    else never
  ) ([],[]) es

let eqSeqTuple : all a. all b.
  ([a] -> [a] -> Bool) -> ([b] -> [b] -> Bool) -> ([a], [b]) -> ([a], [b]) -> Bool =
  lam eqSeql. lam eqSeqr. lam t1. lam t2.
  and (eqSeql t1.0 t2.0) (eqSeqr t1.1 t2.1)

utest eitherPartition [] with ([], []) using eqSeqTuple (eqSeq eqi) (eqSeq eqi)
utest eitherPartition [Left 1, Right "foo", Right "bar", Left 42]
with ([1,42], ["foo", "bar"]) using eqSeqTuple (eqSeq eqi) (eqSeq eqString)
utest eitherPartition [Right 5.0, Right 1.0, Left "42"]
with (["42"], [5.0, 1.0]) using eqSeqTuple (eqSeq eqString) (eqSeq eqf)

--  *-
--  * .brief Extracts the Left values from a list of Eithers.
--  *
--  * .lam[es] List of Eithers whose Left values to extract
--  *
--  * .return The extracted Left values, appearing in the same order as in the
--  *         input list.
-- -*
let eitherLefts: all a. all b. [Either a b] -> [a] = lam es. (eitherPartition es).0

utest eitherLefts [] with [] using eqSeq eqi
utest eitherLefts [Right 1, Right 5] with [] using eqSeq eqi
utest eitherLefts [Right 1, Left "c", Right 5, Left "a"] with ["c", "a"]
using eqSeq eqString

--  *-
--  * .brief Extracts the Right values from a list of Eithers.
--  *
--  * .lam[es] List of Eithers whose Right values to extract
--  *
--  * .return The extracted Right values, appearing in the same order as in the
--  *         input list.
-- -*
let eitherRights: all a. all b. [Either a b] -> [b] = lam es. (eitherPartition es).1

utest eitherRights [] with [] using eqSeq eqi
utest eitherRights [Left "1", Left "5"] with [] using eqSeq eqi
utest eitherRights [Right 1, Left "3", Right 5, Left "1"] with [1, 5]
using eqSeq eqi

--  *-
--  * .brief Checks whether the entered Either value is the Left case.
--  *
--  * .lam[e] The Either value to check
--  *
--  * .return True iff the Either value is the Left case.
-- -*
let eitherIsLeft: all a. all b. Either a b -> Bool = lam e.
  match e with Left _ then true else false

utest eitherIsLeft (Left 5) with true
utest eitherIsLeft (Left "a") with true
utest eitherIsLeft (Right "a") with false
utest eitherIsLeft (Right (Left 1)) with false

--  *-
--  * .brief Checks whether the entered Either value is the Right case.
--  *
--  * .lam[e] The Either value to check
--  *
--  * .return True iff the Either value is the Right case.
-- -*
let eitherIsRight: all a. all b. Either a b -> Bool = lam e.
  match e with Right _ then true else false

utest eitherIsRight (Left 5) with false
utest eitherIsRight (Left "a") with false
utest eitherIsRight (Right "a") with true
utest eitherIsRight (Right (Left 1)) with true

--  *-
--  * .brief Extracts the Left case value from an Either or returns the passed
--  *        default value.
--  *
--  * .lam[v] The default value
--  * .lam[e] The Either value to check
--  *
--  * .return The Left case value or the default value.
-- -*
let eitherFromLeft: all a. all b. a -> Either a b -> a =
  lam v. eitherEither (lam x. x) (lam. v)

utest eitherFromLeft "a" (Right 5) with "a"
utest eitherFromLeft "a" (Left "foo") with "foo"

--  *-
--  * .brief Extracts the Right case value from an Either or returns the passed
--  *        default value.
--  *
--  * .lam[v] The default value
--  * .lam[e] The Either value to check
--  *
--  * .return The Right case value or the default value.
-- -*
let eitherFromRight: all a. all b. b -> Either a b -> b =
  lam v. eitherEither (lam. v) (lam x. x)

utest eitherFromRight 0 (Left "foo") with 0
utest eitherFromRight 0 (Right 42) with 42

--  *-
--  * .brief Extracts the Left case value as an Option.
--  *
--  * .lam[e] The Either value to extract
--  *
--  * .return In the Left case, an Option containing the Left value is
--  *         returned. Otherwise `None ()` is returned.
-- -*
let eitherGetLeft: all a. all b. Either a b -> Option a = lam e.
  match e with Left content then
    Some content
  else
    None ()

utest eitherGetLeft (Left "foo") with Some "foo" using optionEq eqString
utest eitherGetLeft (Right 42) with None () using optionEq eqi

--  *-
--  * .brief Extracts the Right case value as an Option.
--  *
--  * .lam[e] The Either value to extract
--  *
--  * .return In the Right case, an Option containing the Right value is
--  *         returned. Otherwise `None ()` is returned.
-- -*
let eitherGetRight: all a. all b. Either a b -> Option b = lam e.
  match e with Right content then
    Some content
  else
    None ()

utest eitherGetRight (Left "foo") with None () using optionEq eqString
utest eitherGetRight (Right 42) with Some 42 using optionEq eqi
