include "option.mc"
include "bool.mc"

let make = lam n. lam v. create n (lam. v)

utest make 3 5 with [5,5,5]
utest make 4 'a' with ['a', 'a', 'a', 'a']
utest make 0 100 with [] using lam a. lam b. eqi (length a) (length b)

let last = lam seq. get seq (subi (length seq) 1)
let init = lam seq. subsequence seq 0 (subi (length seq) 1)

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
  createRope (length seq) (lam i. get seq i)

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

let for_
  : all a.
     [a]
  -> (a -> ())
  -> ()
  = lam xs. lam f. iter f xs

-- In contrast to map, mapReverse is tail recursive.
let mapReverse = lam f. lam lst.
  foldl (lam acc. lam x. cons (f x) acc) (toList []) lst

utest toRope (mapReverse (lam x. addi x 1) [10,20,30]) with [31,21,11]

-- `mapK f seq k` maps the continuation passing function `f` over the sequence
-- `seq`, passing the result of the mapping to the continuation `k`.
let mapK : all a. all b. all c. (a -> (b -> c) -> c) -> [a] -> ([b] -> c) -> c =
  lam f. lam seq. lam k.
    foldl (lam k. lam x. (lam xs. f x (lam x. k (cons x xs)))) k seq []

utest mapK (lam x. lam k. k (addi x 1)) [] (lam seq. reverse seq) with []
utest mapK (lam x. lam k. k (addi x 1)) [1,2,3] (lam seq. reverse seq) with [4,3,2]
utest mapK (lam x. lam k. k (addi x 1)) [1,2,3] (lam seq. foldl addi 0 seq) with 9

-- Folds
let foldl1 = lam f. lam l. foldl f (head l) (tail l)

utest foldl addi 0 [1,2,3,4,5] with 15
utest foldl addi 0 [] with 0
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16]

let foldr1 = lam f. lam seq. foldr f (last seq) (init seq)

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

let range = lam s. lam e. lam by.
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
      match acc with (acc, [x1] ++ xs1) in (f acc x1 x2, xs1)
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

let zip : all a. all b. [a] -> [b] -> [(a, b)] = zipWith (lam x. lam y. (x, y))

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
  mapAccumL (lam l. lam p : (a, b). (snoc l p.0, p.1)) []

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
  let any = lam p. lam seq.
    if null seq
    then false
    else if p (head seq) then true else any p (tail seq)
end

utest any (lam x. eqi x 1) [0, 4, 1, 2] with true
utest any (lam x. eqi x 5) [0, 4, 1, 2] with false
utest any (lam x. true) [] with false

recursive
  let forAll = lam p. lam seq.
    if null seq
    then true
    else if p (head seq) then forAll p (tail seq)
    else false
end

utest forAll (lam x. eqi x 1) [1, 1, 1, 2] with false
utest forAll (lam x. eqi x 0) [0, 0, 0] with true
utest forAll (lam x. eqi x 1) [] with true

-- Join
let join = lam seqs. foldl concat [] seqs

utest join [[1,2],[3,4],[5,6]] with [1,2,3,4,5,6]
utest join [[1,2],[],[5,6]] with [1,2,5,6]
utest join [[],[],[]] with [] using eqSeq eqi

-- Monadic and Applicative operations

let seqLiftA2
  : all a. all b. all c. (a -> b -> c) -> [a] -> [b] -> [c]
  = lam f. lam as. lam bs.
    join (map (lam a. map (f a) bs) as)

utest seqLiftA2 addi [10, 20, 30] [1, 2, 3]
with [11, 12, 13, 21, 22, 23, 31, 32, 33]

let seqMapM
  : all a. all b. (a -> [b]) -> [a] -> [[b]]
  = lam f. foldr (lam a. lam acc. seqLiftA2 cons (f a) acc) [[]]

-- Searching
recursive
  let filter = lam p. lam seq.
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

recursive
  let find = lam p. lam seq.
    if null seq then None ()
    else if p (head seq) then Some (head seq)
    else find p (tail seq)
end

utest find (lam x. eqi x 2) [4,1,2] with Some 2 using optionEq eqi
utest find (lam x. lti x 1) [4,1,2] with None () using optionEq eqi

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

let partition = lam p. lam seq.
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
let distinct = lam eq. lam seq.
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
let distinctSorted = lam eq. lam s.
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

recursive let merge = lam cmp. lam l. lam r.
  match l with [] then r
  else match r with [] then l
  else match (l, r) with ([x] ++ xs, [y] ++ ys) then
    if leqi (cmp x y) 0 then
      cons x (merge cmp xs r)
    else
      cons y (merge cmp l ys)
  else never
end

recursive let mergeSort = lam cmp. lam seq.
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

let max = lam cmp. min (lam l. lam r. cmp r l)

utest max subi [3,4,8,9,20] with Some 20
utest max subi [9,8,4,20,3] with Some 20
utest max subi [] with None ()

let minOrElse = lam d. lam cmp. lam seq.
  optionGetOrElse d (min cmp seq)

utest minOrElse (lam. 0) subi [3,4,8,9,20] with 3
utest minOrElse (lam. 0) subi [9,8,4,20,3] with 3

let maxOrElse = lam d. lam cmp. minOrElse d (lam l. lam r. cmp r l)

utest maxOrElse (lam. 0) subi [3,4,8,9,20] with 20
utest maxOrElse (lam. 0) subi [9,8,4,20,3] with 20

-- First index in seq that satifies pred
let index = lam pred. lam seq.
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
let lastIndex = lam pred. lam seq.
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

-- Check if s1 is a prefix of s2
recursive let isPrefix = lam eq. lam s1. lam s2.
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
let isSuffix = lam eq. lam s1. lam s2.
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
