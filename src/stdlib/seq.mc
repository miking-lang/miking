include "option.mc"
include "bool.mc"

let make : all a. Int -> a -> [a] = lam n. lam v. create n (lam. v)

utest make 3 5 with [5,5,5]
utest make 4 'a' with ['a', 'a', 'a', 'a']
utest make 0 100 with [] using lam a. lam b. eqi (length a) (length b)

let last : all a. [a] -> a = lam seq. get seq (subi (length seq) 1)
let init : all a. [a] -> [a] = lam seq. subsequence seq 0 (subi (length seq) 1)

utest init [2,3,5] with [2,3]
utest last [2,4,8] with 8

let eqSeq : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> Bool =
  lam eq. lam s1. lam s2.
  recursive let work = lam s1. lam s2.
    match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
      if eq h1 h2 then work t1 t2
      else false
    else true
  in
  let n1 = length s1 in
  let n2 = length s2 in
  let ndiff = subi n1 n2 in
  if eqi ndiff 0 then work s1 s2
  else false

utest eqSeq eqi [] [] with true
utest eqSeq eqi [1] [] with false
utest eqSeq eqi [] [1] with false
utest eqSeq eqi [1] [1] with true
utest eqSeq eqi [1] [2] with false
utest eqSeq eqi [2] [1] with false

-- Converting between List and Rope
let toRope = lam seq.
  recursive let work = lam acc. lam seq.
    match seq with [h] ++ t then
      work (cons h acc) t
    else
      acc
  in
  if isRope seq then seq else
  let s = work [] seq in
  -- NOTE(larshum, 2023-10-24): The below line ensures the elements of the rope
  -- are in the right order, and it also collapses the rope (to ensure
  -- constant-time random access).
  reverse s

let toList = lam seq.
  createList (length seq) (lam i. get seq i)

utest toRope (toList [1,2,3]) with [1,2,3]

-- Maps
let mapOption
  : all a. all b.
     (a -> Option b)
  -> [a]
  -> [b]
  = lam f.
    recursive let work = lam as.
      match as with [a] ++ as then
        match f a with Some b
        then cons b (work as)
        else work as
      else []
    in work

utest mapOption (lam a. if gti a 3 then Some (addi a 30) else None ()) [1, 2, 3, 4, 5, 6]
with [34, 35, 36]

utest mapOption (lam a. if gti a 3 then Some (addi a 30) else None ()) [1, 2]
with [] using eqSeq eqi

utest mapOption (lam a. if gti a 3 then Some (addi a 30) else None ()) []
with [] using eqSeq eqi

let mapiOption
  : all a. all b.
     (Int -> a -> Option b)
  -> [a]
  -> [b]
  = lam f.
    recursive let work = lam idx. lam as.
      match as with [a] ++ as then
        match f idx a with Some b
        then cons b (work (addi idx 1) as)
        else work (addi idx 1) as
      else []
    in work 0

let for_
  : all a.
     [a]
  -> (a -> ())
  -> ()
  = lam xs. lam f. iter f xs

-- In contrast to map, mapReverse is tail recursive.
let mapReverse : all a. all b. (a -> b) -> [a] -> [b] = lam f. lam lst.
  foldl (lam acc. lam x. cons (f x) acc) (toList []) lst

utest toRope (mapReverse (lam x. addi x 1) [10,20,30]) with [31,21,11]

-- Folds
let foldl1 : all a. (a -> a -> a) -> [a] -> a = lam f. lam l. foldl f (head l) (tail l)

utest foldl addi 0 [1,2,3,4,5] with 15
utest foldl addi 0 [] with 0
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16]

let foldr1 : all a. (a -> a -> a) -> [a] -> a = lam f. lam seq. foldr f (last seq) (init seq)

utest foldr (lam x. lam acc. x) 0 [1,2] with 1
utest foldr (lam acc. lam x. x) 0 [] with 0
utest foldr cons [] [1,2,3] with [1,2,3]
utest foldr1 addi [1,2] with 3

recursive
let unfoldr : all a. all c. (a -> Option (c, a)) -> a -> [c] = lam f. lam b0.
  let fb = f b0 in
  match fb with None _ then [] else
  match fb with Some (x, b1) then
    cons x (unfoldr f b1)
  else never
end

utest unfoldr (lam b. if eqi b 10 then None () else Some (b, addi b 1)) 0
with [0,1,2,3,4,5,6,7,8,9]

let range : Int -> Int -> Int -> [Int] = lam s. lam e. lam by.
  unfoldr (lam b. if leqi e b then None () else Some (b, addi b by)) s

utest range 3 5 1 with [3,4] using eqSeq eqi
utest range 3 5 2 with [3] using eqSeq eqi
utest range 3 10 3 with [3,6,9] using eqSeq eqi
utest range (negi 1) 6 2 with [(negi 1), 1, 3, 5] using eqSeq eqi
utest range (negi 1) 2 1 with [negi 1, 0, 1] using eqSeq eqi
utest range 5 3 1 with [] using eqSeq eqi

-- `foldl2 f acc seq1 seq2` left folds `f` over the first
-- min(`length seq1`, `length seq2`) elements in `seq1` and `seq2`, accumuating
-- on `acc`.
recursive
let foldl2 : all a. all b. all c. (a -> b -> c -> a) -> a -> [b] -> [c] -> a =
  lam f. lam acc. lam seq1. lam seq2.
    let g = lam acc : (a, [b]). lam x2.
      match acc with (acc, [x1] ++ xs1) then (f acc x1 x2, xs1)
      else error "foldl2: Cannot happen!"
    in
    if geqi (length seq1) (length seq2) then
      match foldl g (acc, seq1) seq2 with (acc, _) in acc
    else foldl2 (lam acc. lam x1. lam x2. f acc x2 x1) acc seq2 seq1
end

utest foldl2 (lam a. lam x1. lam x2. snoc a (x1, x2)) [] [1, 2, 3] [4, 5, 6]
with [(1, 4), (2, 5), (3, 6)]
utest foldl2 (lam a. lam x1. lam x2. snoc a (x1, x2)) [] [1, 2] [4, 5, 6]
with [(1, 4), (2, 5)]
utest foldl2 (lam a. lam x1. lam x2. snoc a (x1, x2)) [] [1, 2, 3] [4, 5]
with [(1, 4), (2, 5)]

-- `foldli f acc seq` folds over a sequence together with the index of element
-- in the sequence. (Similar to `mapi`)
let foldli: all a. all b. (a -> Int -> b -> a) -> a -> [b] -> a =
  lam fn. lam initAcc. lam seq.
  recursive let work = lam acc. lam i. lam s.
    match s with [e] ++ rest then
      work (fn acc i e) (addi i 1) rest
    else
      acc
  in
  work initAcc 0 seq

utest foldli (lam acc. lam i. lam e: Float. snoc acc (i, e)) [] []
with []
utest foldli (lam acc. lam i. lam e. snoc acc (i, e)) [] [5.0]
with [(0, 5.0)]
utest foldli (lam acc. lam i. lam e. snoc acc (i, e)) [] ["foo", "bar", "babar"]
with [(0, "foo"), (1, "bar"), (2, "babar")]

-- CPS style maps, folds, and iters

-- `mapK f seq k` maps the continuation passing function `f` over the sequence
-- `seq`, passing the result of the mapping to the continuation `k`.
let mapK : all a. all b. all c. (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c =
  lam f. lam seq. lam k.
    foldl (lam k. lam x. (lam xs. f x (lam x. k (snoc xs x)))) k (reverse seq) []

utest mapK (lam x. lam k. k (addi x 1)) [] (lam seq. reverse seq) with []
utest mapK (lam x. lam k. k (addi x 1)) [1,2,3] (lam seq. reverse seq) with [4,3,2]
utest mapK (lam x. lam k. k (addi x 1)) [1,2,3] (lam seq. foldl addi 0 seq) with 9

-- `mapiK f seq k` maps the continuation passing function `f` with the index
-- over the sequence `seq`, passing the result of the mapping to the
-- continuation `k`.
let mapiK : all a. all b. all c. (Int -> a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c =
  lam f. lam seq. lam k.
    (foldl
       (lam ik. match ik with (i, k) in
              lam x. (subi i 1, lam xs. f i x (lam x. k (snoc xs x))))
       (subi (length seq) 1, k) (reverse seq)).1 []

utest mapiK (lam i. lam x. lam k. k (muli x i)) [] (lam seq. reverse seq) with []
utest mapiK (lam i. lam x. lam k. k (muli x i)) [1,2,3] (lam seq. reverse seq)
  with [6,2,0]
utest mapiK (lam i. lam x. lam k. k (muli x i)) [1,2,3] (lam seq. foldl addi 0 seq)
  with 8

-- `foldlK f acc seq k` fold the continuation passing function `f` over the
-- sequence `seq`, from the left, with the initial accumulator `acc` and
-- continuation `k`. (from
-- https://leastfixedpoint.com/tonyg/kcbbs/lshift_archive/folds-and-continuation-passing-style-20070611.html)
let foldlK : all a. all b. all c. all d. (a -> b -> (a -> c) -> c) -> a -> [b] -> (a -> c) -> c
  = lam f. lam acc. lam seq. lam k.
    recursive let recur = lam acc. lam seq. lam k.
      if null seq then k acc
      else f acc (head seq) (lam acc. recur acc (tail seq) k)
    in
    recur acc seq k

utest
  let acc : [Int] = [] in
  utest
    foldlK (lam acc. lam x. lam k. k (cons (addi x 1) acc)) acc [] (lam x. reverse x)
    with []
  in
  utest
    foldlK
      (lam acc. lam x. lam k. k (cons (addi x 1) acc))
      acc
      [1, 2, 3]
      (lam x. reverse x)
    with [2, 3, 4]
  in
  utest
    foldlK
      (lam acc. lam x. lam k.
        if geqi (length acc) 2 then acc -- short circuit
        else k (cons (addi x 1) acc))
      acc
      [1, 2, 3]
      (lam x. reverse x)          -- which also skips this computation
    with [3, 2]
  in
  () with ()

-- `iterK f seq k` iteratively applies the function `f` to the elements of `seq`
-- as long as `()` is passed to its continuation.
let iterK : all a. all b. (a -> (() -> ()) -> ()) -> [a] -> (() -> ()) -> ()
  = lam f. lam seq. lam k.
    recursive let recur = lam seq. lam k.
      if null seq then k ()
      else f (head seq) (lam. recur (tail seq) k)
    in
    recur seq k

utest
  let count = ref 0 in
  let sum = ref 0 in
  let seq = [1, 2, 3, 4] in
  utest
    iterK
      (lam n. lam k.
        modref count (addi (deref count) 1);
        modref sum (addi (deref sum) n);
        k ())
      seq (lam. ())
    with ()
  in
  utest deref count with 4 in
  utest deref sum with 10 in
  modref count 0; modref sum 0;
  utest
    iterK
      (lam n. lam k.
        if eqi n 3 then ()      -- short circuit
        else
          modref count (addi (deref count) 1);
          modref sum (addi (deref sum) n);
          k ())
      seq (lam. ())
    with ()
  in
  utest deref count with 2 in
  utest deref sum with 3 in
  ()
  with ()


-- zips
let zipWith : all a. all b. all c. (a -> b -> c) -> [a] -> [b] -> [c] =
  lam f. foldl2 (lam acc. lam x1. lam x2. snoc acc (f x1 x2)) []

utest zipWith addi [1,2,3,4,5] [5, 4, 3, 2, 1] with [6,6,6,6,6]
utest zipWith (zipWith addi) [[1,2], [], [10, 10, 10]] [[3,4,5], [1,2], [2, 3]]
      with [[4,6], [], [12, 13]] using eqSeq (eqSeq eqi)
utest zipWith addi [] [] with [] using eqSeq eqi

let zipWithIndex : all a. all b. all c. (Int -> a -> b -> c) -> [a] -> [b] -> [c] =
  lam f. lam a1. lam a2.
  recursive let work = lam acc. lam i. lam seq1. lam seq2.
    match seq1 with [e1] ++ seq1tail then
      match seq2 with [e2] ++ seq2tail then
        work (cons (f i e1 e2) acc)
             (addi i 1)
             seq1tail
             seq2tail
      else reverse acc
    else reverse acc
  in
  work (toList []) 0 a1 a2

utest zipWithIndex (lam i. lam a. lam b. addi i (addi a b)) [100, 200, 300] [4000, 5000, 6000]
      with [4100, 5201, 6302] using eqSeq eqi

let zip : all a. all b. [a] -> [b] -> [(a, b)] =
  lam l1. lam l2. zipWith (lam x. lam y. (x, y)) l1 l2

-- Accumulating maps
let mapAccumL : all a. all b. all c. (a -> b -> (a, c)) -> a -> [b] -> (a, [c]) =
  lam f : (a -> b -> (a, c)). lam acc. lam seq.
    foldl
      (lam tacc : (a, [c]). lam x.
         match f tacc.0 x with (acc, y) then (acc, snoc tacc.1 y) else never)
      (acc, []) seq

let mapAccumR : all a. all b. all c. (a -> b -> (a, c)) -> a -> [b] -> (a, [c]) =
  lam f : (a -> b -> (a, c)). lam acc. lam seq.
    foldr
      (lam x. lam tacc : (a, [c]).
         match f tacc.0 x with (acc, y) then (acc, cons y tacc.1) else never)
       (acc, []) seq

utest mapAccumL (lam acc. lam x. let x = addi x 1 in ((addi acc x), x)) 0 [1,2,3]
with (9, [2,3,4])
utest mapAccumL (lam acc. lam x. ((cons x acc), x)) [] [1,2,3]
with ([3,2,1], [1,2,3])
utest mapAccumR (lam acc. lam x. let x = addi x 1 in ((addi acc x), x)) 0 [1,2,3]
with (9, [2,3,4])
utest mapAccumR (lam acc. lam x. ((cons x acc), x)) [] [1,2,3]
with ([1,2,3], [1,2,3])

let unzip : all a. all b. [(a, b)] -> ([a], [b]) =
  lam l. mapAccumL (lam l. lam p : (a, b). (snoc l p.0, p.1)) [] l

-- `iter2 f seq1 seq1` iterativly applies `f` to the first
-- min(`length seq1`, `length seq2`) elements in `seq1` and `seq2`.
let iter2 : all a. all b. (a -> b -> ()) -> [a] -> [b] -> () =
  lam f. lam seq1. lam seq2.
    let f = lam x : (a, b). match x with (x1, x2) in f x1 x2 in
    iter f (zip seq1 seq2)

utest
  let r = ref [] in
  let s1 = [1, 2, 3, 4] in
  let s2 = [0, 1, 2, 3] in
  let f = lam x1. lam x2. modref r (snoc (deref r) (subi x1 x2)) in
  utest iter2 f s1 s2 with () in
  deref r
with [1, 1, 1, 1]

utest
  let r = ref [] in
  let s1 = [1, 2, 3, 4, 5] in
  let s2 = [0, 1, 2, 3] in
  let f = lam x1. lam x2. modref r (snoc (deref r) (subi x1 x2)) in
  utest iter2 f s1 s2 with () in
  deref r
with [1, 1, 1, 1]

-- Predicates
recursive
  let any : all a. (a -> Bool) -> [a] -> Bool = lam p. lam seq.
    if null seq
    then false
    else if p (head seq) then true else any p (tail seq)
end

utest any (lam x. eqi x 1) [0, 4, 1, 2] with true
utest any (lam x. eqi x 5) [0, 4, 1, 2] with false
utest any (lam x. true) [] with false

recursive
  let forAll : all a. (a -> Bool) -> [a] -> Bool = lam p. lam seq.
    if null seq
    then true
    else if p (head seq) then forAll p (tail seq)
    else false
end

utest forAll (lam x. eqi x 1) [1, 1, 1, 2] with false
utest forAll (lam x. eqi x 0) [0, 0, 0] with true
utest forAll (lam x. eqi x 1) [] with true

-- Monadic and Applicative operations

let join : all a. [[a]] -> [a] = lam seqs. foldl concat [] seqs

utest join [[1,2],[3,4],[5,6]] with [1,2,3,4,5,6]
utest join [[1,2],[],[5,6]] with [1,2,5,6]
utest join [[],[],[]] with [] using eqSeq eqi

let joinMap : all a. all b. (a -> [b]) -> [a] -> [b] =
  lam f. lam a.
    foldl (lam s. lam x. concat s (f x)) [] a

utest joinMap (lam x. [subi (muli x 2) 1, muli x 2]) [1,2,3] with [1,2,3,4,5,6]
utest joinMap
        (lam x. if eqi 1 (modi x 2) then [subi (muli x 2) 1, muli x 2] else [])
        [1,2,3]
with [1,2,5,6]

let seqLiftA2
  : all a. all b. all c. (a -> b -> c) -> [a] -> [b] -> [c]
  = lam f. lam as. lam bs.
    if null bs then [] else
      joinMap (lam a. map (f a) bs) as

utest seqLiftA2 addi [10, 20, 30] [1, 2, 3]
with [11, 12, 13, 21, 22, 23, 31, 32, 33]

let seqLiftA3
  : all a. all b. all c. all d. (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
  = lam f. lam as. lam bs. lam cs.
  joinMap (lam a. seqLiftA2 (f a) bs cs) as

utest seqLiftA3 (lam x. lam y. lam z. addi (addi x y) z)
        [100, 200, 300] [10, 20, 30] [1, 2, 3]
with [ 111, 112, 113, 121, 122, 123, 131, 132, 133
     , 211, 212, 213, 221, 222, 223, 231, 232, 233
     , 311, 312, 313, 321, 322, 323, 331, 332, 333 ]

let seqMapM
  : all a. all b. (a -> [b]) -> [a] -> [[b]]
  = lam f.
    recursive let work = lam g. lam a. lam bs.
      match bs with [b] ++ bs then
        match g a b with a & ![] then work g a bs
        else []
      else a
    in
    work (lam acc. lam a. seqLiftA2 snoc acc (f a)) [[]]

utest seqMapM (lam x. [x, addi x 1]) [10, 20, 30]
with [ [10, 20, 30], [10, 20, 31], [10, 21, 30], [10, 21, 31]
     , [11, 20, 30], [11, 20, 31], [11, 21, 30], [11, 21, 31] ]

-- Searching
recursive
  let filter : all a. (a -> Bool) -> [a] -> [a] = lam p. lam seq.
    if null seq then []
    else if p (head seq) then cons (head seq) (filter p (tail seq))
    else (filter p (tail seq))
end

utest filter (lam x. eqi x 1) [1,2,4] with [1]
utest filter (lam. false) [3,5,234,1,43] with [] using eqSeq eqi
utest filter (lam x. gti x 2) [3,5,234,1,43] with [3,5,234,43]

recursive let filterOption : all a. [Option a] -> [a] =
  lam optSeq.
  match optSeq with [Some x] ++ optSeq then cons x (filterOption optSeq)
  else match optSeq with [None _] ++ optSeq then filterOption optSeq
  else []
end

utest filterOption [Some 3, Some 2, None (), Some 4] with [3, 2, 4] using eqSeq eqi
utest filterOption [None (), None ()] with [] using eqSeq eqi
utest filterOption [None (), Some 1, None (), Some 1] with [1, 1] using eqSeq eqi

-- Find the first element in a sequence satisfying a predicate in a list.
recursive
  let find : all a. (a -> Bool) -> [a] -> Option a = lam p. lam seq.
    if null seq then None ()
    else if p (head seq) then Some (head seq)
    else find p (tail seq)
end

utest find (lam x. eqi x 2) [4,1,2] with Some 2 using optionEq eqi
utest find (lam x. lti x 1) [4,1,2] with None () using optionEq eqi

-- Find the last element in a sequence satisfying a predicate in a list.
let findLast : all a. (a -> Bool) -> [a] -> Option a = lam p. lam seq.
  find p (reverse seq)

utest findLast (lam x. lti x 1) [4,1,2] with None () using optionEq eqi

-- Find the first index in a sequence whose element satisfies a predicate
let findi : all a. (a -> Bool) -> [a] -> Option Int = lam p. lam seq.
  recursive let work = lam p. lam seq. lam i.
    if null seq then None ()
    else if p (head seq) then Some i
    else work p (tail seq) (addi i 1)
  in
  work p seq 0

utest findi (lam x. eqi x 5) [4,5,2,5] with Some 1 using optionEq eqi
utest findi (lam x. eqi x 0) [4,1,2] with None () using optionEq eqi

-- Find the last index in a sequence whose element satisfies a predicate
let findiLast : all a. (a -> Bool) -> [a] -> Option Int = lam p. lam seq.
  recursive let work = lam p. lam seq. lam i.
    if null seq then None ()
    else if p (last seq) then Some i
    else work p (init seq) (subi i 1)
  in
  work p seq (subi (length seq) 1)

utest findiLast (lam x. eqi x 5) [4,5,2,5] with Some 3 using optionEq eqi
utest findiLast (lam x. eqi x 0) [4,1,2] with None () using optionEq eqi

let seqMem : all a. (a -> a -> Bool) -> [a] -> a -> Bool = lam eq. lam xs. lam x.
  foldl or false (map (eq x) xs)

utest seqMem eqi [1,2,3] 1 with true
utest seqMem eqi [1,2,3] 0 with false
utest seqMem eqi [] 0 with false

recursive
  let findMap : all a. all b. (a -> Option b) -> [a] -> Option b = lam f. lam seq.
    match seq with [h] ++ t then
      match f h with Some x then Some x else findMap f t
    else None ()
end

utest findMap (lam x. if geqi x 3 then Some (muli x 2) else None ()) [1,2,3]
with Some 6 using optionEq eqi
utest findMap (lam x. if eqi x 0 then Some x else None ()) [1,2,3]
with None () using optionEq eqi

-- NOTE(larshum, 2023-05-02): Finds the minimum index in the given sequence for
-- which applying the provided function yields a non-negative value. If there
-- is no such element in the sequence, None is returned instead.
--
-- This function assumes the sequence is sorted according to the provided
-- sequence, in the sense that 'map f s' yields a sequence of integers in
-- increasing order.
let lowerBoundBinarySearch : all a. (a -> Int) -> [a] -> Option Int = lam f. lam s.
  recursive let work = lam first. lam count.
    if gti count 0 then
      let step = divi count 2 in
      let idx = addi first step in
      if lti (f (get s idx)) 0 then
        work (addi first (addi step 1)) (subi count (addi step 1))
      else work first step
    else first
  in
  let idx = work 0 (length s) in
  if eqi idx (length s) then None ()
  else Some idx

let s = [0,1,2,3,4,5,6,7,8,9]
utest lowerBoundBinarySearch (lam x. x) s with Some 0
utest lowerBoundBinarySearch (lam x. subi x 9) s with Some 9
utest lowerBoundBinarySearch (lam x. subi x 5) s with Some 5
utest lowerBoundBinarySearch (lam x. subi x 12) s with None ()
utest lowerBoundBinarySearch (lam x. subi x 1) [0,0,0,0,1,1,1,1,1,1] with Some 4
utest lowerBoundBinarySearch (lam x. floorfi x) [negf 0.5,negf 0.3,negf 0.1,0.6,1.2]
with Some 3

let partition : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam p. lam seq.
  recursive let work = lam l. lam r. lam seq.
    match seq with [] then (l, r)
    else match seq with [s] ++ seq then
      if p s then work (cons s l) r seq
      else work l (cons s r) seq
    else never
  in work [] [] (reverse seq)

utest partition (lam x. gti x 3) [4,5,78,1] with ([4,5,78],[1])
utest partition (lam x. gti x 0) [4,5,78,1] with ([4,5,78,1],[])
using lam a : ([Int], [Int]). lam b : ([Int], [Int]).
  if eqSeq eqi a.0 b.0 then eqSeq eqi a.1 b.1 else false

-- Removes duplicates with preserved ordering. Keeps first occurrence of an element.
let distinct : all a. (a -> a -> Bool) -> [a] -> [a] = lam eq. lam seq.
  recursive let work = lam seq1. lam seq2.
    match seq1 with [h] ++ t
      then match find (eq h) seq2 with Some _
           then work t seq2
           else cons h (work t (cons h seq2))
    else []
  in work seq []

utest distinct eqi [] with [] using eqSeq eqi
utest distinct eqi [42,42] with [42]
utest distinct eqi [1,1,2] with [1,2]
utest distinct eqi [1,1,5,1,2,3,4,5,0] with [1,5,2,3,4,0]

-- Removes duplicated elements in a sorted sequence. More efficient than the
-- 'distinct' function.
let distinctSorted : all a. (a -> a -> Bool) -> [a] -> [a]  = lam eq. lam s.
  recursive let work = lam acc. lam s.
    match s with [h1] ++ t then
      match acc with [h2] ++ _ then
        if eq h1 h2 then work acc t
        else work (cons h1 acc) t
      else work [h1] t
    else acc
  in
  reverse (work [] s)

utest distinctSorted eqi [] with [] using eqSeq eqi
utest distinctSorted eqi [42,42] with [42]
utest distinctSorted eqi [1,1,2] with [1,2]
utest distinctSorted eqi [0,1,1,1,2,3,4,5,5] with [0,1,2,3,4,5]

-- Sorting
recursive
let quickSort : all a. (a -> a -> Int) -> ([a] -> [a]) = lam cmp. lam seq.
  if null seq then seq else
    let h = head seq in
    let t = tail seq in
    let lr = partition (lam x. lti (cmp x h) 0) t in
    concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
end

recursive let merge : all a. (a -> a -> Int) -> [a] -> [a] -> [a] = lam cmp. lam l. lam r.
  match l with [] then r
  else match r with [] then l
  else match (l, r) with ([x] ++ xs, [y] ++ ys) then
    if leqi (cmp x y) 0 then
      cons x (merge cmp xs r)
    else
      cons y (merge cmp l ys)
  else never
end

recursive let mergeSort : all a. (a -> a -> Int) -> [a] -> [a] = lam cmp. lam seq.
  match seq with [] then []
  else match seq with [x] then [x]
  else
    let lr = splitAt seq (divi (length seq) 2) in
    merge cmp (mergeSort cmp lr.0) (mergeSort cmp lr.1)
end

let sort = quickSort

utest quickSort subi [3,4,8,9,20] with [3,4,8,9,20]
utest quickSort subi [9,8,4,20,3] with [3,4,8,9,20]
utest quickSort (lam l. lam r. subi r l) [9,8,4,20,3] with [20,9,8,4,3]
utest quickSort (lam l. lam r. 0) [9,8,4,20,3] with [9,8,4,20,3]
utest quickSort subi [] with [] using eqSeq eqi

utest mergeSort subi [3,4,8,9,20] with [3,4,8,9,20]
utest mergeSort subi [9,8,4,20,3] with [3,4,8,9,20]
utest mergeSort (lam l. lam r. subi r l) [9,8,4,20,3] with [20,9,8,4,3]
utest mergeSort (lam l. lam r. 0) [9,8,4,20,3] with [9,8,4,20,3]
utest mergeSort subi [] with [] using eqSeq eqi


-- Max/Min
let minIdx : all a. (a -> a -> Int) -> [a] -> Option (Int, a) =
  lam cmp : a -> a -> Int. lam seq : [a].
    if null seq then None ()
    else
      match foldl (
        lam acc : (Int, Int, a). lam e : a.
          match acc with (curi, mini, m) in
          if lti (cmp m e) 0 then (addi curi 1, mini, m)
          else (addi curi 1, curi, e)
        ) (1, 0, head seq) (tail seq)
      with (_,i,m) in Some (i,m)

utest minIdx subi [3,4,8,9,20] with Some (0,3)
utest minIdx subi [9,8,4,20,3] with Some (4,3)
utest minIdx subi [] with None ()

let min : all a. (a -> a -> Int) -> [a] -> Option a = lam cmp. lam seq.
  optionMap (lam r. match r with (_,m) in m) (minIdx cmp seq)

utest min subi [3,4,8,9,20] with Some 3
utest min subi [9,8,4,20,3] with Some 3
utest min subi [] with None ()

let max : all a. (a -> a -> Int) -> [a] -> Option a = lam cmp. min (lam l. lam r. cmp r l)

utest max subi [3,4,8,9,20] with Some 20
utest max subi [9,8,4,20,3] with Some 20
utest max subi [] with None ()

let minOrElse : all a. (() -> a) -> (a -> a -> Int) -> [a] -> a = lam d. lam cmp. lam seq.
  optionGetOrElse d (min cmp seq)

utest minOrElse (lam. 0) subi [3,4,8,9,20] with 3
utest minOrElse (lam. 0) subi [9,8,4,20,3] with 3

let maxOrElse : all a. (() -> a) -> (a -> a -> Int) -> [a] -> a = lam d. lam cmp. minOrElse d (lam l. lam r. cmp r l)

utest maxOrElse (lam. 0) subi [3,4,8,9,20] with 20
utest maxOrElse (lam. 0) subi [9,8,4,20,3] with 20

-- First index in seq that satifies pred
let index : all a. (a -> Bool) -> [a] -> Option Int = lam pred. lam seq.
  recursive let index_rechelper = lam i. lam pred. lam seq.
    if null seq then
      None ()
    else if pred (head seq) then
      Some i
    else
      index_rechelper (addi i 1) pred (tail seq)
  in
  index_rechelper 0 pred seq

utest index (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]]
      with Some 1 using optionEq eqi
utest index (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]]
      with Some 4 using optionEq eqi

-- Last index in seq that satisfies pred
let lastIndex : all a. (a -> Bool) -> [a] -> Option Int = lam pred. lam seq.
  recursive let lastIndex_rechelper = lam i. lam acc. lam pred. lam seq.
    if null seq then
      acc
    else if pred (head seq) then
      lastIndex_rechelper (addi i 1) (Some i) pred (tail seq)
    else
      lastIndex_rechelper (addi i 1) acc pred (tail seq)
  in
  lastIndex_rechelper 0 (None ()) pred seq

utest lastIndex (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]]
      with Some 3 using optionEq eqi
utest lastIndex (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]]
      with Some 4 using optionEq eqi

-- Return a sequence of all indices for which the corresponding element
-- satisfies the predicate.
let indices : all a. (a -> Bool) -> [a] -> [Int] = lam pred. lam seq.
  recursive let rec = lam i. lam acc. lam seq.
    if null seq then acc
    else if pred (head seq) then rec (addi i 1) (cons i acc) (tail seq)
    else rec (addi i 1) acc (tail seq)
  in reverse (rec 0 [] seq)

utest indices (eqi 1) [1,2,3,1,2,3,1,2,3,1] with [0,3,6,9] using eqSeq eqi

-- Check if s1 is a prefix of s2
recursive let isPrefix : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> Bool
  = lam eq. lam s1. lam s2.
    if null s1 then true
    else if null s2 then false
    else and (eq (head s1) (head s2)) (isPrefix eq (tail s1) (tail s2))
end

utest isPrefix eqi [] [1,2,3] with true
utest isPrefix eqi [1] [1,2,3] with true
utest isPrefix eqi [1,2,3] [1,2,3] with true
utest isPrefix eqi [1,2,3,4] [1,2,3] with false
utest isPrefix eqi [2,3] [1,2,3] with false

-- Check if s1 is a suffix of s2
let isSuffix : all a. all b. (a -> b -> Bool) -> [a] -> [b] -> Bool
  = lam eq. lam s1. lam s2.
    isPrefix eq (reverse s1) (reverse s2)

utest isSuffix eqi [] [1,2,3] with true
utest isSuffix eqi [2,3] [1,2,3] with true
utest isSuffix eqi [1,2,3] [1,2,3] with true
utest isSuffix eqi [1,2,3] [1,1,2,3] with true
utest isSuffix eqi [1,1,2,3] [1,2,3] with false

let seqCmp : all a. (a -> a -> Int) -> [a] -> [a] -> Int = lam cmp. lam s1. lam s2.
  recursive let work = lam s1. lam s2.
    match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
      let c = cmp h1 h2 in
      if eqi c 0 then work t1 t2
      else c
    else 0
  in
  let n1 = length s1 in
  let n2 = length s2 in
  let ndiff = subi n1 n2 in
  if eqi ndiff 0 then work s1 s2
  else ndiff

utest seqCmp subi [] [] with 0
utest seqCmp subi [1,2,3] [1,2,3] with 0
utest
  match lti (seqCmp subi [1,2] [1,2,3]) 0 with true then true else false
with true
utest
  match gti (seqCmp subi [1,2,3] [1,2]) 0 with true then true else false
with true
utest
  match lti (seqCmp subi [1,1] [1,2]) 0 with true then true else false
with true
utest
  match gti (seqCmp subi [1,2] [1,1]) 0 with true then true else false
with true

-- Select an index uniformly at random.
let randIndex : all a. [a] -> Option Int = lam seq.
  match seq with [] then None ()
  else Some (randIntU 0 (length seq))

utest
  match randIndex [] with None () then true else false
with true
utest randIndex [1] with Some 0
utest
  match randIndex [1,2] with Some (0 | 1) then true else false
with true

-- Select an element uniformly at random.
let randElem : all a. [a] -> Option a = lam seq.
  optionMap (get seq) (randIndex seq)

utest
  match randElem [] with None () then true else false
with true
utest randElem [1] with Some 1
utest
  match randElem [1,2] with Some (1 | 2) then true else false
with true

-- Permute the order of elements according to a sequence of integers, which is
-- assumed to represent the target position of the elements in the permuted
-- sequence.
let permute : all a. [a] -> [Int] -> [a] = lam elems. lam permutation.
  if eqi (length elems) (length permutation) then
    let ordered = sort (lam x : (a, Int). lam y : (a, Int). subi x.1 y.1)
                       (zip elems permutation) in
    match unzip ordered with (orderedElems, _) then
      orderedElems
    else never
  else error "Expected sequences of equal length"

utest permute "abc" [1, 2, 0] with "cab"
utest permute "xy" [0, 1] with "xy"
utest permute "abcd" [0, 3, 1, 2] with "acdb"
utest permute [0, 1, 2] [2, 0, 1] with [1, 2, 0]

-- Given a list xs, create a list of all pairs (xs[i], xs[j]) 
-- where i < j.
recursive let pairWithLater : all a. [a] -> [(a, a)] = lam lst.
  match lst with [x] ++ xs then
    concat (map (lam y. (x, y)) xs) (pairWithLater xs)
  else 
    []
end
utest pairWithLater [1,2,3] with [(1, 2), (1, 3), (2, 3)] using eqSeq (lam x. lam y. and (eqi x.0 y.0) (eqi x.1 y.1))
utest pairWithLater [1] with [] using eqSeq (lam x. lam y. and (eqi x.0 y.0) (eqi x.1 y.1))
utest pairWithLater [] with [] using eqSeq (lam x. lam y. and (eqi x.0 y.0) (eqi x.1 y.1))


-- Concatenate a sequence of sequences [s1, s2, ..., sn], interleaving each
-- sequence si on a delimiter
recursive
  let seqJoin: all a. [a] -> [[a]] -> [a] = lam delim. lam ss.
  if null ss
  then []
  else if eqi (length ss) 1
       then head ss
       else concat (concat (head ss) delim) (seqJoin delim (tail ss))
end

utest seqJoin [7,7] [[1,2,3], [4,5,6], [0,0]] with [1,2,3,7,7,4,5,6,7,7,0,0]
utest seqJoin [] [[1,2,3],[4,5,6]] with [1,2,3,4,5,6]
utest seqJoin [7,7,7,7,7] [[1,2,3]] with [1,2,3]
utest seqJoin [7,7,7,7] [] with []


-- Replace all occurrences of the provided sequence `check` by another sequence
-- `replacement`, in order of left to right.
let subseqReplace: all a. (a -> a -> Bool) -> [a] -> [a] -> [a] -> [a] =
    lam eq. lam check. lam replacement. lam seq.
    -- Ignore empty check sequences
    if null check then seq
    else --continue
    recursive let work = lam checkIdx. lam seqIdx. lam acc.
      if eqi checkIdx (length check) then -- found match
        work 0 seqIdx (concat acc replacement)
      else if eqi seqIdx (length seq) then -- base case, end of sequence
        concat acc (subsequence seq (subi seqIdx checkIdx) (addi checkIdx 1))
      else
        let eCheck = get check checkIdx in
        let eSeq = get seq seqIdx in
        if eq eCheck eSeq then
          work (addi checkIdx 1) (addi seqIdx 1) acc
        else
          let seqIdx = subi seqIdx checkIdx in
          work 0 (addi seqIdx 1) (snoc acc (get seq seqIdx))
    in
    work 0 0 []

utest subseqReplace eqi [] [10] [1,1,1] with [1,1,1]
utest subseqReplace eqi [1] [2] [1,1,1] with [2,2,2]
utest subseqReplace eqi [1] [2] [3,1,3] with [3,2,3]
utest subseqReplace eqi [1,1] [2,2] [3,1,3,1,1,1] with [3,1,3,2,2,1]
utest subseqReplace eqi [1,1] [2] [3,1,3,1,1] with [3,1,3,2]
utest subseqReplace eqi [3,4,5] [42,42] [1,2,3,4,5,6,7] with [1,2,42,42,6,7]
utest subseqReplace eqi [1,1] [100,101,100] [0,1,0,1,2,1,1,3,4,0,0,1,1,0,1,0] with [0,1,0,1,2,100,101,100,3,4,0,0,100,101,100,0,1,0]
utest subseqReplace eqi [1,1] [2] [3,4,3] with [3,4,3]
utest subseqReplace eqi [0,1,2] [88] [0,0,1,2,100,0,1] with [0,88,100,0,1]
