-- A simple example involving operations on sequences

include "common.mc"
include "string.mc"

let sum : [Int] -> Int = lam s.
  foldl addi 0 s

let multiplyBy : Int -> [Int] -> [Int] = lam n. lam s.
  map (muli n) s

mexpr

let n = 1000 in
let s = create n (lam. randIntU 0 1000) in

let cpuSum = sum (multiplyBy 4 s) in
printLn (int2string cpuSum);
let gpuSum = accelerate (sum (multiplyBy 4 s)) in
printLn (int2string gpuSum);
if eqi cpuSum gpuSum then
  printLn "CPU and GPU agreed on the sum"
else
  printLn "CPU and GPU found different sums"
