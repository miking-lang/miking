-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Parallel operations over sequences.

include "thread-pool.mc"
include "seq.mc"

let _split = lam seq. lam chunkSize.
  recursive let work = lam acc. lam n. lam xs.
    if leqi n chunkSize then
      cons xs acc
    else match splitAt xs chunkSize with (chunk, xs) then
      work (cons chunk acc) (subi n chunkSize) xs
    else never
  in reverse (work [] (length seq) seq)

utest _split [1,2,3] 1 with [[1], [2], [3]]
utest _split [1,2,3,4,5,6] 4 with [[1,2,3,4], [5,6]]
utest _split [] 4 with [[]]

-- Join for lists
let _joinLists = lam seqs. foldl concat (createList 0 (lam. 0)) seqs

-- Reverse map for lists
let _mapReverseList = lam f. lam lst.
  foldl (lam acc. lam x. cons (f x) acc) (createList 0 (lam. 0)) lst

-- 'pmap pool nbrChunks f s' applies 'f' to all elements in 's' in parallel,
-- using the thread pool 'pool'. The sequence 's' is splitted into
-- min(nbrChunks, length s) chunks, where each chunk is operated on in parallel.
let pmap : ThreadPool -> Int -> (a -> b) -> [a] -> [b] =
  lam pool. lam nbrChunks. lam f. lam seq.
    if eqi nbrChunks 1 then map f seq
    else
      let len = length seq in
      let nbrChunks = if gti nbrChunks len then len else nbrChunks in
      let div = divi len nbrChunks in
      let rem = modi len nbrChunks in
      let chunkSize = addi div rem in
      if isList seq then
        -- List: split into chunks
        let chunks = _split seq chunkSize in
        utest forAll isList chunks with true in
        let tasks = map (lam chunk. threadPoolAsync pool (lam. reverse (_mapReverseList f chunk))) chunks in
        _joinLists (map (threadPoolWait pool) tasks)
      else if true then
        let chunks = _split seq chunkSize in
        let tasks = map (lam chunk. threadPoolAsync pool (lam. map f chunk)) chunks in
        join (map (threadPoolWait pool) tasks)
      else
        -- Rope: access elements with offset
        let lastIdx = subi nbrChunks 1 in
        let tasks = map (lam chunkIdx.
            let start = muli chunkIdx chunkSize in
            let len =
              if eqi chunkIdx lastIdx then
                if eqi rem 0 then chunkSize else rem
              else chunkSize
            in
            threadPoolAsync pool (lam. map f (subsequence seq start len)))
          (create nbrChunks (lam i. i))
        in
        join (map (threadPoolWait pool) tasks)

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 1 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 2 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 56 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 3 (lam i. addi i 1) (createList 3 (lam i. i)) in
  threadPoolTearDown pool;
  res
with [1,2,3]
