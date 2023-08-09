-- Example showing that records and tuples can be used within the CPU code and
-- the accelerated code exclusively. It also shows one way to transfer them to
-- the accelerated code.

include "math.mc" --eqfApprox
include "seq.mc" -- eqSeq

type Data = {a : Int, b : Float}

let getInt : Data -> Int = lam d. d.a
let getFloat : Data -> Float = lam d. d.b

let eqData : Data -> Data -> Bool = lam d1. lam d2.
  if eqi d1.a d2.a then
    eqfApprox 1e-6 d1.b d2.b
  else false

let accSumToInt : Int -> Float -> Int = lam a. lam b.
  addi a (floorfi b)

let sumToInt : Data -> Data = lam d.
  {d with a = accSumToInt d.a d.b}

mexpr

let s : [Data] = create 100 (lam i. {a = i, b = int2float i}) in

-- Using the Data record within the CPU code is straightforward.
let s1 : [Data] = map sumToInt s in

-- As we cannot pass the record between CPU and accelerated code, we have to
-- manually destruct it, and manually reconstruct the result in the CPU code.
let sa : [Int] = map getInt s in
let sb : [Float] = map getFloat s in
let sx : [Int] = accelerate (map2 accSumToInt sa sb) in
let s2 : [Data] =
  map
    (lam d : (Int, Float). {a = d.0, b = d.1})
    (zip sx sb) in

utest s1 with s2 using eqSeq eqData in

-- We compute the sum by storing the sum of both in the first argument, and
-- then computing the sum of these.
let sum1 : Int =
  let s : [Data] = map sumToInt s in
  foldl (lam acc : Int. lam d : Data. addi acc d.a) 0 s in

-- We can safely use the data type, as long as it only exists within the
-- accelerated code.
let sum2 : Int = accelerate (
  let s : [Data] = map2 (lam a : Int. lam b : Float. {a = a, b = b}) sa sb in
  let s : [Data] = map sumToInt s in
  let sa : [Int] = map getInt s in
  reduce addi 0 sa) in

utest sum1 with sum2 in

()
