-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test integer primitives

include "option.mc"
include "string.mc"

mexpr

-- Matching unit
utest () with () in
utest () with {} in

-- Matching integers
utest
  match 1 with 1 then true else false
  with true
in
utest
  match -1 with -1 then true else false
  with true
in
utest
  match negi 1 with -1 then true else false
  with true
in

-- Constructor with arguments
type T a in
con K1 : all a. a -> T a in
con K2 : all a. a -> T a in
con K3 : all a. a -> T a in

let eqT : all a. (a -> a -> Bool) -> T a -> T a -> Bool =
  lam elemEq. lam t1. lam t2.
  let m = (t1, t2) in
  match m with (K1 l, K1 r) then
    elemEq l r
  else match m with (K2 l, K2 r) then
    elemEq l r
  else match m with (K3 l, K3 r) then
    elemEq l r
  else false
in

let eqUnit = lam t1 : (). lam t2 : ().
  match (t1, t2) with ((), ()) then true else false
in

let eqStringIntTuple = lam t1 : (String, Int). lam t2 : (String, Int).
  match (t1, t2) with ((s1, i1), (s2, i2)) then
    and (eqString s1 s2) (eqi i1 i2)
  else false
in

utest K2() with K2() using eqT eqUnit in
utest match K2() with K2 a then a else () with () using eqUnit in
utest K3("k",100) with K3("k",100) using eqT eqStringIntTuple in
utest
  match K2("k",100) with K2 x then
    let x : (String, Int) = x in
    x.0
  else "a"
with "k" using eqString in


-- Matching two constructors
type FooBar a b in
con Foo : all a. all b. a -> FooBar a b in
con Bar : all a. all b. b -> FooBar a b in

let f = lam x : FooBar (String, Int) Int.
  match x with Foo (s,n) then
    (n,s)
  else
  match x with Bar b then (addi b 5, "b") else
  (negi 1, "b") in
utest f (Foo("a",1)) with (1, "a") in
utest f (Bar 10) with (15, "b") in


-- Counting values in a binary tree
type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in

recursive
  let count = lam tree.
    match tree with Node (left,right) then
      addi (count left) (count right)
    else match tree with Leaf v then
      v
    else error "Unknown node"
in

let tree1 = Leaf(5) in
utest count tree1 with 5 in

let tree2 = Node(Leaf(2),Leaf(7)) in
utest count tree2 with 9 in

let tree3 = Node(Node(Leaf(3),Node(Leaf(2),Leaf(6))),Leaf(12)) in
utest count tree3 with 23 in

recursive
  let count = lam tree.
    match tree with Node(left,right) then
      addi (count left) (count right)
    else match tree with Leaf v then
      v
    else error "Unknown node"
in

utest count tree3 with 23 in

recursive
  let count = lam tree.
    match tree with Node {#label"0"=left,#label"1"=right} then
      addi (count left) (count right)
    else match tree with Leaf v then
      v
    else error "Unknown node"
in

utest count tree3 with 23 in

--- Nested record patterns

utest
  match {foo=7,bar={more="hello"}} with {foo=_,bar={more=str}} then str else ""
with "hello" in

-- Wildcard
utest match (1,2,3) with (_,2,_) then true else false with true in
utest match (1,2,3) with (_,2,x) then x else 0 with 3 in

-- Helper equality functions
let eqIntIntEmptySeqTuple =
  lam t1 : (Int, Int, [(Int, Char)]). lam t2 : (Int, Int, [(Int, Char)]).
  and (eqi t1.0 t2.0)
    (and (eqi t1.1 t2.1) (and (eqi (length t1.2) (length t2.2)) (eqi (length t1.2) 0)))
in

-- Matching sequences
let s1 = [1,3,5,10] in
utest match s1 with [1,3] then true else false with false in
utest match s1 with [1,3,5,10] then true else false with true in
utest match s1 with [1,3] ++ _ then true else false with true in
utest match s1 with [2,3] ++ _ then true else false with false in
utest match s1 with [1,a] ++ _ then a else 0 with 3 in
utest match s1 with [b] ++ _ then let a = 2 in (a, b, []) else (0, 0, [])
with (2, 1, []) using eqIntIntEmptySeqTuple in
utest match s1 with _ ++ [b] then let a = 2 in (a, b, []) else (0, 0, [])
with (2, 10, []) using eqIntIntEmptySeqTuple in
utest match s1 with [_,a] ++ b then (a,b) else (0,[]) with (3,[5,10]) in
utest match s1 with _ ++ [5,10] then true else false with true in
utest match s1 with _ ++ [5,11] then true else false with false in
utest match s1 with _ ++ [5,a] then a else 0 with 10 in
utest match s1 with first ++ [1,2] then true else false with false in
utest match s1 with [1,x] ++ rest then (x,rest) else (0,[]) with (3,[5,10]) in
utest match s1 with first ++ [x,y] then (x,y,first) else (0,0,[]) with (5,10,[1,3]) in
utest match s1 with first ++ [x,y,10] then (first,x,y) else ([],0,0) with ([1],3,5) in
utest match s1 with [1] ++ mid ++ [10] then mid else [] with [3, 5] in
utest match s1 with [1,3] ++ mid ++ [10] then mid else [] with [5] in
utest match s1 with [a,b] ++ mid ++ [c] then (a, b, mid, c) else (0, 0, [], 0) with (1, 3, [5], 10) in
utest match s1 with [] ++ _ then true else false with true in
--utest match true with [] ++ _ then true else false with false in

utest match "foo" with ['f','o','o'] then true else false with true in
utest match "foo" with "foo" then true else false with true in
utest match "foobar" with "fo" ++ rest then rest else "" with "obar" in
utest match "foobar" with first ++ "bar" then first else "" with "foo" in
utest match "" with first then first else "-" with "" in
utest match "" with first then first else "-" with "" in
utest match "" with [] then true else false with true in
utest match "" with [] ++ rest then rest else "foo" with [] in
utest match "" with first ++ [] then first else "foo" with [] in
utest match "foobar" with "fo" ++ mid ++ "ar" then mid else "" with "ob" in
utest match "foobar" with "fob" ++ mid ++ "ar" then mid else "" with "" in

utest match [["a","b"],["c"]] with [a] then true else false with false in
utest match [["a","b"],["c"]] with [a,b] then (a,b) else ([],[]) with (["a","b"],["c"]) in
utest match (1,[["a","b"],["c"]],76) with (1,[a,b],0) then true else false with false in
utest match (1,[["a","b"],["c"]],76) with (1,[a,b],76) then (a,b) else ([],[]) with (["a","b"],["c"]) in
utest match (1,[["a","b"],["c"]],76) with (1,[a]++b,76) then (a,b) else ([],[]) with (["a","b"],[["c"]]) in
utest match (1,[["a","b"],["c"]],76) with (1,b++[a],76) then (a,b) else ([],[]) with (["c"],[["a","b"]]) in
utest match (1,[["a","b"],["c"]],76) with (1,b++[["c"]],76) then b else [] with [["a","b"]] in

-- Matching with records
--utest match {} with {blue = _} then true else false with false in
utest match {blue = true} with {blue = _} then true else false with true in
utest match {blue = true} with {blue = a} then a else false with true in
utest match {blue = (1, 2)} with {blue = {}} then true else false with true in
utest match {blue = (1, 2)} with {blue = ()} then true else false with true in
utest match {blue = (1, 2)} with {blue = (1,3)} then true else false with false in
utest match {blue = {red = true}} with {blue = {}} then true else false with true in
utest match {blue = true, red = true} with {blue = _} & {red = _} then true else false with true in
--utest match {blue = true} with {blue = _} & {red = _} then true else false with false in

-- Matching with tuples
utest match ("foo", "bar") with ("foo", "bar") then true else false with true in
utest match ("foo", "bar") with ("foo", _) then true else false with true in
utest match ("foo", "bar") with (_, "foo") then true else false with false in
utest match ("foo",) with ("foo",) then true else false with true in
utest match ("foo",) with (_,) then true else false with true in
utest match ("foo",) with ("bar",) then true else false with false in

-- Matching with "&", "|", "!"
utest match true with !_ then true else false with false in
utest match (1, 2) with (a, _) & (_, b) then (a, b) else (0, 0) with (1, 2) in
utest match K1 1 with K1 a | K2 a | K3 a then a else 0 with 1 in
utest match K2 2 with K1 a | K2 a | K3 a then a else 0 with 2 in
utest match K3 3 with K1 a | K2 a | K3 a then a else 0 with 3 in
utest match (true, true) with (true, a) & !(_, true) then a else false with false in
utest match (true, false) with (true, a) & !(_, true) then a else false with false in
utest match (1, 2) with (a, _) & b then (a, b) else (0, (0, 0)) with (1, (1, 2)) in
utest match Some true with a & !(None ()) then a else Some false
with Some true using optionEq eqBool in
utest match None () with a & !(None ()) then a else Some false
with Some false using optionEq eqBool in
utest match "abc" with ['a'] ++ s | ['b'] ++ s then s else "" with "bc" in
utest match "bc" with ['a'] ++ s | ['b'] ++ s then s else "" with "c" in

-- Matching with never terms
let x = true in
utest match x with true then "true" else
      match x with false then "false" else
      never
with "true" in

()
