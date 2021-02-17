include "bool.mc"
include "option.mc"

let make = lam n. lam v. create n (lam _. v)

utest make 3 5 with [5,5,5]
utest make 4 'a' with ['a', 'a', 'a', 'a']
utest make 0 100 with []

let null = lam seq. eqi 0 (length seq)
let head = lam seq. get (splitAt seq 1).0 0
let tail = lam seq. (splitAt seq 1).1
let last = lam seq. get (splitAt seq (subi (length seq) 1)).1 0
let init = lam seq. (splitAt seq (subi (length seq) 1)).0

utest head [2,3,5] with 2
utest tail [2,4,8] with [4,8]
utest init [2,3,5] with [2,3]
utest last [2,4,8] with 8

let slice = lam seq. lam off. lam cnt.
  let seq = (splitAt seq off).1 in
  let cnt = if gti cnt (length seq) then length seq else cnt in
  (splitAt seq cnt).0

utest slice [1,3,5] 0 2 with [1,3]
utest slice [3,7,10,20] 1 3 with [7,10,20]
utest slice ['a','b'] 1 10 with ['b']
utest slice [1,3] 2 10 with []

-- Maps
let mapi = lam f. lam seq.
  recursive let work = lam i. lam f. lam seq.
      if null seq then []
      else cons (f i (head seq)) (work (addi i 1) f (tail seq))
  in
  work 0 f seq

let map = lam f. mapi (lam _. lam x. f x)

utest mapi (lam i. lam x. i) [3,4,8,9,20] with [0,1,2,3,4]
utest mapi (lam i. lam x. i) [] with []
utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21]
utest map (lam x. addi x 1) [] with []

-- Folds
recursive
  let foldl = lam f. lam acc. lam seq.
    if null seq then acc
    else foldl f (f acc (head seq)) (tail seq)
end

let foldl1 = lam f. lam l. foldl f (head l) (tail l)

utest foldl addi 0 [1,2,3,4,5] with 15
utest foldl addi 0 [] with 0
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16]

recursive
  let foldr = lam f. lam acc. lam seq.
    if null seq
    then acc
    else f (head seq) (foldr f acc (tail seq))
end

let foldr1 = lam f. lam seq. foldr f (last seq) (init seq)

utest foldr (lam x. lam acc. x) 0 [1,2] with 1
utest foldr (lam acc. lam x. x) 0 [] with 0
utest foldr cons [] [1,2,3] with [1,2,3]
utest foldr1 (lam x. lam acc. (x,acc)) [1,2] with (1,2)

recursive
let unfoldr = lam f. lam b.
  let fb = f b in
  match fb with None _ then [] else
  match fb with Some (a, bp) then cons a (unfoldr f bp)
  else never
end

utest unfoldr (lam b. if eqi b 10 then None () else Some (b, addi b 1)) 0
with [0,1,2,3,4,5,6,7,8,9]

let zipWith = lam f. lam seq1. lam seq2.
  recursive let work = lam a. lam s1. lam s2.
    if or (null s1) (null s2) then a
    else
      work (snoc a (f (head s1) (head s2))) (tail s1) (tail s2)
  in
  work [] seq1 seq2

utest zipWith addi [1,2,3,4,5] [5, 4, 3, 2, 1] with [6,6,6,6,6]
utest zipWith (zipWith addi) [[1,2], [], [10, 10, 10]] [[3,4,5], [1,2], [2, 3]]
      with [[4,6], [], [12, 13]]
utest zipWith addi [] [] with []

-- Accumulating maps
let mapAccumL : (a -> b -> (a, c)) -> a -> [b] -> (a, [c]) =
  lam f. lam acc. lam seq.
    foldl
      (lam tacc. lam x.
         match f tacc.0 x with (acc, y) then (acc, snoc tacc.1 y) else never)
      (acc, []) seq

let mapAccumR : (a -> b -> (a, c)) -> a -> [b] -> (a, [c]) =
  lam f. lam acc. lam seq.
    foldr
      (lam x. lam tacc.
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

let unzip : [(a, b)] -> ([a], [b]) = mapAccumL (lam l. lam p. (snoc l p.0, p.1)) []

-- Predicates
recursive
  let any = lam p. lam seq.
    if null seq
    then false
    else or (p (head seq)) (any p (tail seq))
end

utest any (lam x. eqi x 1) [0, 4, 1, 2] with true
utest any (lam x. eqi x 5) [0, 4, 1, 2] with false
utest any (lam x. true) [] with false

recursive
  let all = lam p. lam seq.
    if null seq
    then true
    else and (p (head seq)) (all p (tail seq))
end

utest all (lam x. eqi x 1) [1, 1, 1, 2] with false
utest all (lam x. eqi x 0) [0, 0, 0] with true
utest all (lam x. eqi x 1) [] with true

-- Join
let join = lam seqs. foldl concat [] seqs

utest join [[1,2],[3,4],[5,6]] with [1,2,3,4,5,6]
utest join [[1,2],[],[5,6]] with [1,2,5,6]
utest join [[],[],[]] with []

-- Searching
recursive
  let filter = lam p. lam seq.
    if null seq then []
    else if p (head seq) then cons (head seq) (filter p (tail seq))
    else (filter p (tail seq))
end

utest filter (lam x. eqi x 1) [1,2,4] with [1]
utest filter (lam _. false) [3,5,234,1,43] with []
utest filter (lam x. gti x 2) [3,5,234,1,43] with [3,5,234,43]

recursive
  let find = lam p. lam seq.
    if null seq then None ()
    else if p (head seq) then Some (head seq)
    else find p (tail seq)
end

utest find (lam x. eqi x 2) [4,1,2] with Some 2
utest find (lam x. lti x 1) [4,1,2] with None ()

let partition = (lam p. lam seq.
    (filter p seq, filter (lam q. if p q then false else true) seq))

utest partition (lam x. gti x 3) [4,5,78,1] with ([4,5,78],[1])
utest partition (lam x. gti x 0) [4,5,78,1] with ([4,5,78,1],[])

-- Removes duplicates with preserved ordering. Keeps first occurrence of an element.
let distinct = lam eq. lam seq.
  recursive let work = lam seq1. lam seq2.
    match seq1 with [h] ++ t
      then match find (eq h) seq2 with Some _
           then work t seq2
           else cons h (work t (cons h seq2))
    else []
  in work seq []

utest distinct eqi [] with []
utest distinct eqi [42,42] with [42]
utest distinct eqi [1,1,2] with [1,2]
utest distinct eqi [1,1,5,1,2,3,4,5,0] with [1,5,2,3,4,0]

-- Sorting
recursive
let quickSort = lam cmp. lam seq.
  if null seq then seq else
    let h = head seq in
    let t = tail seq in
    let lr = partition (lam x. lti (cmp x h) 0) t in
    concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
end

let sort = quickSort

utest sort (lam l. lam r. subi l r) [3,4,8,9,20] with [3,4,8,9,20]
utest sort (lam l. lam r. subi l r) [9,8,4,20,3] with [3,4,8,9,20]
utest sort (lam l. lam r. subi r l) [9,8,4,20,3] with [20,9,8,4,3]
utest sort (lam l. lam r. 0) [9,8,4,20,3] with [9,8,4,20,3]
utest sort (lam l. lam r. subi l r) [] with []

-- Max/Min
let min = lam cmp. lam seq.
  recursive let work = lam e. lam seq.
    if null seq then Some e
    else
      let h = head seq in
      let t = tail seq in
      if lti (cmp e h) 0 then work e t else work h t
  in
  if null seq then None () else work (head seq) (tail seq)

utest min (lam l. lam r. subi l r) [3,4,8,9,20] with Some 3
utest min (lam l. lam r. subi l r) [9,8,4,20,3] with Some 3
utest min (lam l. lam r. subi l r) [] with None ()

let max = lam cmp. min (lam l. lam r. cmp r l)

utest max (lam l. lam r. subi l r) [3,4,8,9,20] with Some 20
utest max (lam l. lam r. subi l r) [9,8,4,20,3] with Some 20
utest max (lam l. lam r. subi l r) [] with None ()

let minOrElse = lam d. lam cmp. lam seq.
  optionGetOrElse d (min cmp seq)

utest minOrElse (lam _. 0) (lam l. lam r. subi l r) [3,4,8,9,20] with 3
utest minOrElse (lam _. 0) (lam l. lam r. subi l r) [9,8,4,20,3] with 3

let maxOrElse = lam d. lam cmp. minOrElse d (lam l. lam r. cmp r l)

utest maxOrElse (lam _. 0) (lam l. lam r. subi l r) [3,4,8,9,20] with 20
utest maxOrElse (lam _. 0) (lam l. lam r. subi l r) [9,8,4,20,3] with 20

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

utest index (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 1
utest index (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 4

-- Last index in seq that satifies pred
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

utest lastIndex (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 3
utest lastIndex (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 4

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
