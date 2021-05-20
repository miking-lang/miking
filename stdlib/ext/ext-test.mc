include "seq.mc"

external extTestListOfLists : [[Int]]
utest extTestListOfLists with [[0]]

external extTestListHeadHead : [[a]] -> a
utest extTestListHeadHead [[0]] with 0

external extTestArrayOfArrays : [[Int]]
utest extTestArrayOfArrays with [[0]]

external extTestArrayHeadHead : [[a]] -> a
utest extTestArrayHeadHead [[0]] with 0

external extTestFlip : (a -> b -> c) -> b -> a -> c
utest extTestFlip (lam x. lam y. subi x y) 1 2 with 1

external extTestTuple1 : (Int, Float)
utest extTestTuple1.0 with 1

external extTestTuple2 : ([Int], Int)
utest extTestTuple2.0 with [1]

external extTestTuple0th1 : (Int, Float) -> Int
utest extTestTuple0th1 (1, 2.) with 2

external extTestTuple0th2 : ([Int], Int) -> [Int]
utest extTestTuple0th2 ([1], 2) with [2]
