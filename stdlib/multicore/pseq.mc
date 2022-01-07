-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Parallel operations over sequences.

include "thread-pool.mc"
include "seq.mc"

-- Helpers for supporting lists --

let _rope2List = lam s1.
  createList (length s1) (lam i. get s1 i)

utest _rope2List [1,2,3] with createList 3 (lam i. addi i 1) using eqSeq eqi

-- Reverse map for lists (tail recursive)
let _mapReverseList = lam f. lam lst.
  foldl (lam acc. lam x. cons (f x) acc) (createList 0 (lam. 0)) lst

-- Reverse join for lists (tail recursive)
let _joinReverseList = lam seqs.
  let seqs = reverse seqs in
  recursive let work = lam acc. lam seqs.
    match seqs with [] then acc
    else match seqs with [s] ++ seqs in
      recursive let inner = lam acc. lam s.
        match s with [] then acc
        else match s with [x] ++ s in inner (cons x acc) s
      in work (inner acc s) seqs
  in work [] seqs

utest _joinReverseList [_rope2List [2,1], _rope2List [5,4,3], _rope2List [8,7,6]]
with _rope2List [1,2,3,4,5,6,7,8]
using eqSeq eqi

-- End list helpers --

-- Split a sequence into chunks of size 'chunkSize'
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

-- 'pmap pool nbrChunks f s' applies 'f' to all elements in 's' in parallel,
-- using the thread pool 'pool'. The sequence 's' is splitted into
-- min(nbrChunks, length s) chunks, where each chunk is operated on in parallel.
let pmap : ThreadPool -> Int -> (a -> b) -> [a] -> [b] =
  lam pool. lam nbrChunks. lam f. lam seq.
    if eqi nbrChunks 1 then
      if isList seq then reverse (_mapReverseList f seq)
      else map f seq
    else
      let len = length seq in
      let chunkSize = addi (divi len nbrChunks) (modi len nbrChunks) in
      let chunks = _split seq chunkSize in
      if isList seq then
        utest forAll isList chunks with true in
        let tasks = map (lam chunk. threadPoolAsync pool (lam. _mapReverseList f chunk)) chunks in
        _joinReverseList (map (threadPoolWait pool) tasks)
      else
        let tasks = map (lam chunk. threadPoolAsync pool (lam. map f chunk)) chunks in
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

-- Large list to test for stack overflow
utest
  let pool = threadPoolCreate 4 in
  let res = pmap pool 8 (lam i. addi i 1) (createList 1000000 (lam i. i)) in
  threadPoolTearDown pool;
  length res
with 1000000
