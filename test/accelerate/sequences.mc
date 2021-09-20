-- A simple example involving operations on sequences

include "common.mc"
include "string.mc"

let sum : [Int] -> Int = lam s.
  foldl addi 0 s

let sum2d : [[Int]] -> Int = lam s.
  sum (map sum s)

mexpr

let n = 1000 in
let m = 5000 in
let s : [[Int]] = create m (lam. create n (lam. randIntU 0 1000)) in

let cpuSum = sum2d s in
printLn (int2string cpuSum);
let gpuSum = accelerate (sum2d s) in
printLn (int2string gpuSum);
if eqi cpuSum gpuSum then
  printLn "OCaml and accelerated agreed on the sum"
else
  printLn "OCaml and accelerated found different sums"
