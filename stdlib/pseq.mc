include "seq.mc"
include "common.mc"
include "multicore/thread-pool.mc"

let pool = threadPoolGlobal

let split = lam seq. lam chunkSize.
  recursive let work = lam acc. lam n. lam xs.
    if leqi n chunkSize then
      cons xs acc
    else match splitAt xs chunkSize with (chunk, xs) then
      work (cons chunk acc) (subi n chunkSize) xs
    else never
  in reverse (work [] (length seq) seq)

utest split [1,2,3] 1 with [[1], [2], [3]] using eqSeq (eqSeq eqi)
utest split [1,2,3,4,5,6] 4 with [[1,2,3,4], [5,6]] using eqSeq (eqSeq eqi)
utest split [] 4 with [[]] using eqSeq (eqSeq eqi)

let chunkWork : [a] -> ([a] -> b) -> [b] = lam seq. lam f.
  let chunkSize = HoleIntRange {min = 1, max = 1000, depth = 2, default = 10} in
  let chunks = split seq chunkSize in
  let tasks = map (lam chunk. threadPoolAsync pool (lam. f chunk)) chunks in
  map threadPoolWait tasks

let pmap = lam f. lam seq.
  join (chunkWork seq (map f))

utest pmap (lam i. i) [1,2,3] with [1,2,3]

let pfold = lam f. lam acc. lam seq.
  foldl f acc (chunkWork seq (foldl f acc))

utest pfold addi 0 (create 101 (lam i. i)) with 5050

let piter = lam f. lam seq.
  chunkWork seq (iter f); ()

-- utest piter (lam. print "hello ") [1,2,3] with ()
