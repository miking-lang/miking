// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test the parsing of types

// No type in lambda
let f = lam x. addi x 2 in
utest f 5 with 7 in

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



()
