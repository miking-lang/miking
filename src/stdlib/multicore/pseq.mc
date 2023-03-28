-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Parallel operations over sequences.

include "thread-pool.mc"
include "seq.mc"

-- Reverse join for lists (tail recursive)
let _joinReverseList = lam seqs.
  let seqs = reverse seqs in
  recursive let work = lam acc. lam seqs.
    if null seqs then acc
    else
      recursive let inner = lam acc. lam s.
        if null s then acc
        else inner (cons (head s) acc) (tail s)
      in work (inner acc (head seqs)) (tail seqs)
  in work (toList []) seqs

utest
  let res = _joinReverseList [toList [2,1], toList [5,4,3], toList [8,7,6]] in
  utest isList res with true in
  toRope res
with [1,2,3,4,5,6,7,8]

-- Split a sequence into chunks of size 'chunkSize'
let _split : all a. [a] -> Int -> [[a]] = lam seq. lam chunkSize.
  recursive let work = lam acc. lam n. lam xs.
    if leqi n chunkSize then
      cons xs acc
    else match splitAt xs chunkSize with (chunk, xs) then
      work (cons chunk acc) (subi n chunkSize) xs
    else never
  in reverse (work [] (length seq) seq)

utest _split [1,2,3] 1 with [[1], [2], [3]]
utest _split [1,2,3,4,5,6] 4 with [[1,2,3,4], [5,6]]
utest _split [] 4 with [[]] using eqSeq (eqSeq eqi)

-- 'pmap pool nbrChunks f s' applies 'f' to all elements in 's' in parallel,
-- using the thread pool 'pool'. The sequence 's' is splitted into
-- min(nbrChunks, length s) chunks, where each chunk is operated on in parallel.
-- The representation of the sequence is unchanged: a list as input gives a list
-- as output, and vice versa for Ropes.
let pmap : all a. all b. ThreadPool [b] -> Int -> (a -> b) -> [a] -> [b] =
  lam pool. lam nbrChunks. lam f. lam seq.
    if eqi nbrChunks 1 then
      if isList seq then reverse (mapReverse f seq)
      else map f seq
    else
      let len = length seq in
      let chunkSize = addi (divi len nbrChunks) (modi len nbrChunks) in
      let chunks = _split seq chunkSize in
      if isList seq then
        utest forAll isList chunks with true in
        let tasks = map (lam chunk. threadPoolAsync pool (lam. mapReverse f chunk)) chunks in
        _joinReverseList (map (threadPoolWait pool) tasks)
      else
        let tasks = map (lam chunk. threadPoolAsync pool (lam. map f chunk)) chunks in
        join (map (threadPoolWait pool) tasks)

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 1 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  utest isRope res with true in
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 2 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  utest isRope res with true in
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 56 (lam i. addi i 1) [1,2,3] in
  threadPoolTearDown pool;
  utest isRope res with true in
  res
with [2,3,4]

utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 3 (lam i. addi i 1) (createList 3 (lam i. i)) in
  threadPoolTearDown pool;
  utest isList res with true in
  toRope res
with [1,2,3]

-- Large list to test for stack overflow
utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 8 (lam i. addi i 1) (createList 1000000 (lam i. i)) in
  threadPoolTearDown pool;
  utest isList res with true in
  length res
with 1000000
