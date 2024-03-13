-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test the parsing of types

include "math.mc"

mexpr

-- No type in lambda
let f = lam x. addi x 2 in
utest f 5 with 7 in

-- Unit type
let a:() = () in
utest (lam x:(). 7) a with 7 in

-- Int type
let v : Int = 5 in
let f = lam x:Int. muli x 5 in
utest f 5 with 25 in

-- Float type
let v : Float = 3.33 in
let f = lam x:Float. mulf x 10.0 in
utest f v with 33.3 using eqf in

-- Bool type
let v : Bool = true in
utest (lam x:Bool. if x then 1 else 2) v with 1 in

-- Function type
let f1 : Int -> Int = lam x. addi x 1 in
utest f1 5 with 6 in
let f2 : Int -> Float -> Float = lam x:Int. lam y:Float. addf (int2float x) y in
utest f2 10 17.2 with 27.2 using eqf in

-- Polymorphic type
let f : all a. a -> a = lam x. x in
utest f 5 with 5 in

-- Tuple type
let eqIntFloatTuple = lam t1 : (Int, Float). lam t2 : (Int, Float).
  if eqi t1.0 t2.0 then eqf t1.1 t2.1 else false
in
let eqIntFloatIntTuple = lam t1 : (Int, Float, Int). lam t2 : (Int, Float, Int).
  if eqi t1.0 t2.0 then
    if eqf t1.1 t2.1 then eqi t1.2 t2.2 else false
  else false
in

let x0 : Int = 7 in
let x1 : (Int) = (8) in
let x2 : (Int,Float) = (7, 33.3) in
let x3 : (Int,Float,Int) = (1, 2.2, 7) in
utest x0 with 7 in
utest x1 with 8 in
utest x2 with (7, 33.3) using eqIntFloatTuple in
utest x3 with (1, 2.2, 7) using eqIntFloatIntTuple in
utest (lam x:(Int,Float). x.0) (8, 13.3) with 8 in

-- String type
let s:String = "yes" in
utest (lam x:String. concat x x) s with "yesyes" in

-- Sequence type
let l1 : [Int] = [1,3,4,8] in
utest (lam x:[Int]. get x 2) l1 with 4 in

-- Data types
type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in
let t : (Tree, Tree) = match Node(Leaf(5),Leaf(10)) with Node t then t else error "" in
utest t.0 with Leaf(5) in

-- Type alias
type Tree2 = Tree in

-- Constructor types
let f : all a :: {Tree[> ]}. Tree{a} -> Int =
  lam x. match x with Leaf l then l else 0
in
utest f (Leaf 5) with 5 in

let f : all a :: {Tree[< Node Leaf]}. Tree{a} -> Int =
  lam x. match x with Leaf l then l else
           match x with Node _ then 0 else never
in
utest f (Leaf 5) with 5 in

let f : all a :: {Tree[| Node Leaf]}. Tree{a} -> Tree{a} =
  lam x. match x with Leaf l then Leaf l else
           match x with Node t then Node t else never
in
utest f (Node (Leaf 5, Leaf 10)) with (Node (Leaf 5, Leaf 10)) in

type Wood in
con TreeWood : Tree -> Wood in

con WoodTree : Wood -> Tree in

let t : all a :: {Wood[> TreeWood], Tree[> Node Leaf WoodTree]}. Tree{a} =
  Node (WoodTree (TreeWood (Leaf 5)), Leaf 10)
in
utest match t with Node (WoodTree (TreeWood (Leaf l)), _) then l else error "" with 5 in

()
