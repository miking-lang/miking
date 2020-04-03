// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test the parsing of types

mexpr

// No type in lambda
let f = lam x. addi x 2 in
utest f 5 with 7 in

// Unit type
let a:() = () in
utest (lam x:(). 7) a with 7 in

// Dynamic type
let f = lam x:Dyn. x in
utest f 5 with 5 in

// Int type
let v : Int = 5 in
let f = lam x:Int. muli x 5 in
utest f 5 with 25 in

// Float type
let v : Float = 3.33 in
let f = lam x:Float. mulf x 10.0 in
utest f v with 33.3 in

// Bool type
let v : Bool = true in
utest (lam x:Bool. if x then 1 else 2) v with 1 in

// Function type
let f1 : Int -> Int = lam x. addi x 1 in
utest f1 5 with 6 in
let f2 : Int -> Float -> Float = lam x:Int. lam y:Float. addf (int2float x) y in
utest f2 10 17.2 with 27.2 in

// Tuple type
let x0 : Int = 7 in
let x1 : (Int) = (8) in
let x2 : (Int,Float) = (7, 33.3) in
let x3 : (Int,Float,Int) = (1, 2.2, 7) in
utest x0 with 7 in
utest x1 with 8 in
utest x2 with (7, 33.3) in
utest x3 with (1, 2.2, 7) in
utest (lam x:(Int,Float). x.0) (8, 13.3) with 8 in

// String type
let s:String = "yes" in
utest (lam x:String. concat x x) s with "yesyes" in

// Sequence type
let l1 : [Int] = [1,3,4,8] in
utest (lam x:[Int]. get x 2) l1 with 4 in

// Data types
type Tree in
con Node : (Tree,Tree) -> Tree in
con Leaf : (Int) -> Tree in
let t : Tree = match Node(Leaf(5),Leaf(10)) with Node t then t else error "" in
utest t.0 with Leaf(5) in

// Type alias
type Tree2 = Tree in


()
