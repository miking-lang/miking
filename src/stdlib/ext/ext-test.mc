-- This file contains tests for externals. The corresponding ocaml functions
-- are defined in exttest.ml

include "seq.mc"

include "common.mc"
mexpr


external extTestListOfLists : [[Int]] in
utest extTestListOfLists with [[0]] in

external extTestListHeadHead : all a. [[a]] -> a in
utest extTestListHeadHead [[0]] with 0 in

external extTestArrayOfArrays : [[Int]] in
utest extTestArrayOfArrays with [[0]] in

external extTestArrayHeadHead : all a. [[a]] -> a in
utest extTestArrayHeadHead [[0]] with 0 in

external extTestFlip : all a. all b. all c. (a -> b -> c) -> b -> a -> c in
utest extTestFlip (lam x. lam y. subi x y) 1 2 with 1 in

external extTestUnit1 : Int -> () in
utest extTestUnit1 1 with () in

external extTestUnit2 : () -> Int in
utest extTestUnit2 () with 1 in

external extTestTuple1 : (Int, Float) in
utest extTestTuple1.0 with 1 in
utest extTestTuple1.1 with 3. using eqf in

external extTestTuple2 : ([Int], Int) in
utest extTestTuple2.0 with [1] in
utest extTestTuple2.1 with 2 in

external extTestTuple10th : (Int, Float) -> Int in
utest extTestTuple10th (1, 3.) with 2 in

external extTestTuple20th : ([Int], Int) -> [Int] in
utest extTestTuple20th ([1], 2) with [2] in

external extTestRecord1 : {c : Int, d : Float} in
utest extTestRecord1.c with 1 in
utest extTestRecord1.d with 3. using eqf in

external extTestRecord1A : {c : Int, d : Float} -> Int in
utest extTestRecord1A {c = 1, d = 3.} with 2 in

external extTestRecord2 : {c : [Int], d : Int} in
utest extTestRecord2.c with [1] in
utest extTestRecord2.d with 2 in

external extTestRecord2A : {c : [Int], d : Int} -> [Int] in
utest extTestRecord2A {c = [1], d = 2} with [2] in

external extTestRecord3 : {c : {c : Int, d : Float}, d : {c : [Int], d : Int}} in
utest extTestRecord3.c.c with 1 in
utest extTestRecord3.c.d with 3. using eqf in
utest extTestRecord3.d.c with [1] in
utest extTestRecord3.d.d with 2 in

external extTestRecord3BA
  : {c : {c : Int, d : Float}, d : {c : [Int], d : Int}} -> [Int]
in
utest extTestRecord3BA {c = {c = 1, d = 3.}, d = {c = [1], d = 2}} with [2] in

external extTestArgLabel : Int -> Int -> Int in
utest extTestArgLabel 2 1 with 1 in

let t = tensorCreateCArrayInt [1] (lam. 1) in

external extTestGenarrIntNumDims : Tensor[Int] -> Int in
utest extTestGenarrIntNumDims t with 1 in

external extTestGenarrIntSliceLeft : Tensor[Int] -> [Int] -> Tensor[Int] in
utest tensorRank (extTestGenarrIntSliceLeft t [0]) with 0 in

let t = tensorCreateCArrayFloat [1] (lam. 1.) in

external extTestGenarrFloatNumDims : Tensor[Float] -> Int in
utest extTestGenarrFloatNumDims t with 1 in

external extTestGenarrFloatSliceLeft : Tensor[Float] -> [Int] -> Tensor[Float]
in
utest tensorRank (extTestGenarrFloatSliceLeft t [0]) with 0 in

let t = tensorCreateCArrayInt [1, 1] (lam. 1) in

external extTestArray2IntSliceLeft : Tensor[Int] -> Int -> Tensor[Int] in
utest tensorRank (extTestArray2IntSliceLeft t 0) with 1 in

external extTestArray2IntOfGenarr : Tensor[Int] -> Tensor[Int] in
utest tensorRank (extTestArray2IntOfGenarr t) with 2 in

let t = tensorCreateCArrayFloat [1, 1] (lam. 1.) in

external extTestArray2FloatSliceLeft : Tensor[Float] -> Int -> Tensor[Float] in
utest tensorRank (extTestArray2FloatSliceLeft t 0) with 1 in

external extTestArray2FloatOfGenarr : Tensor[Float] -> Tensor[Float] in
utest tensorRank (extTestArray2FloatOfGenarr t) with 2 in

()
