-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test integer primitives

mexpr

-- Constructor with and without arguments
con K1 in
con K2 in
con K3 in
utest K1 with K1 in
utest match K1 with K1 then 1 else 0 with 1 in
utest K2() with K2() in
utest match K2() with K2 a then a else () with () in
utest K3("k",100) with K3("k",100) in
utest match K2("k",100) with K2 x then x.0 else "a" with "k" in


-- Matching two constructors
con Foo in
con Bar in
let f = lam x.
   match x with Foo t then
     let s = t.0 in
     let n = t.1 in
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
    match tree with Node t then
      let left = t.0 in
      let right = t.1 in
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


-- Wildcard
utest match (1,2,3) with (_,2,_) then true else false with true in
utest match (1,2,3) with (_,2,x) then x else 0 with 3 in

-- Matching sequences
let s1 = [1,3,5,10] in
utest match s1 with [1,3] then true else false with false in
utest match s1 with [1,3,5,10] then true else false with true in
utest match s1 with [1,3] ++ _ then true else false with true in
utest match s1 with [2,3] ++ _ then true else false with false in
utest match s1 with [1,a] ++ _ then a else 0 with 3 in
utest match s1 with [_,a] ++ b then (a,b) else (0,[]) with (3,[5,10]) in
utest match s1 with _ ++ [5,10] then true else false with true in
utest match s1 with _ ++ [5,11] then true else false with false in
utest match s1 with _ ++ [5,a] then a else 0 with 10 in
utest match s1 with first ++ [1,2] then true else false with false in
utest match s1 with [1,x] ++ rest then (x,rest) else (0,[]) with (3,[5,10]) in
utest match s1 with first ++ [x,y] then (x,y,first) else (0,0,[]) with (5,10,[1,3]) in
utest match s1 with first ++ [x,y,10] then (first,x,y) else ([],0,0) with ([1],3,5) in

utest match "foo" with ['f','o','o'] then true else false with true in
utest match "foo" with "foo" then true else false with true in
utest match "foobar" with "fo" ++ rest then rest else "" with "obar" in
utest match "foobar" with first ++ "bar" then first else "" with "foo" in
utest match "" with first then first else "-" with "" in
utest match "" with first then first else "-" with "" in
utest match "" with [] then true else false with true in
utest match "" with [] ++ rest then rest else "foo" with [] in
utest match "" with first ++ [] then first else "foo" with [] in

utest match [["a","b"],["c"]] with [a] then true else false with false in
utest match [["a","b"],["c"]] with [a,b] then (a,b) else [] with (["a","b"],["c"]) in
utest match (1,[["a","b"],["c"]],76) with (1,[a,b],0) then true else false with false in
utest match (1,[["a","b"],["c"]],76) with (1,[a,b],76) then (a,b) else [] with (["a","b"],["c"]) in
utest match (1,[["a","b"],["c"]],76) with (1,[a]++b,76) then (a,b) else [] with (["a","b"],[["c"]]) in
utest match (1,[["a","b"],["c"]],76) with (1,b++[a],76) then (a,b) else [] with (["c"],[["a","b"]]) in
utest match (1,[["a","b"],["c"]],76) with (1,b++[["c"]],76) then b else [] with [["a","b"]] in






()
