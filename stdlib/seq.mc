include "option.mc"

let null = lam seq. eqi 0 (length seq)
let head = lam seq. get (splitAt seq 1).0 0
let tail = lam seq. (splitAt seq 1).1
let last = lam seq. get (splitAt seq (subi (length seq) 1)).1 0
let init = lam seq. (splitAt seq (subi (length seq) 1)).0

let slice = lam seq. lam off. lam cnt.
  let seq = (splitAt seq off).1 in
  let cnt = if gti cnt (length seq) then length seq else cnt in
  (splitAt seq cnt).0

-- Maps and (un)folds
let mapi = lam f. lam seq.
  recursive let work = lam i. lam f. lam seq.
      if null seq then []
      else cons (f i (head seq)) (work (addi i 1) f (tail seq))
  in
  work 0 f seq

let map = lam f. mapi (lam _. lam x. f x)

recursive
  let foldl = lam f. lam acc. lam seq.
    if null seq then acc
    else foldl f (f acc (head seq)) (tail seq)
end
let foldl1 = lam f. lam l. foldl f (head l) (tail l)

recursive
  let foldr = lam f. lam acc. lam seq.
    if null seq
    then acc
    else f (head seq) (foldr f acc (tail seq))
end

let foldr1 = lam f. lam seq. foldr f (last seq) (init seq)

let zipWith = lam f. lam seq1. lam seq2.
  recursive let work = lam a. lam s1. lam s2.
    if or (null s1) (null s2) then a
    else
      work (snoc a (f (head s1) (head s2))) (tail s1) (tail s2)
  in
  work [] seq1 seq2

recursive
let unfoldr = lam f. lam b.
  let fb = f b in
  match fb with None _ then [] else
  match fb with Some (a, bp) then cons a (unfoldr f bp)
  else error "unfoldr.impossible"
end

-- Predicates
recursive
  let any = lam p. lam seq.
    if null seq
    then false
    else or (p (head seq)) (any p (tail seq))
end

recursive
  let all = lam p. lam seq.
    if null seq
    then true
    else and (p (head seq)) (all p (tail seq))
end

-- Join
let join = lam seqs. foldl concat [] seqs

-- Searching
recursive
  let filter = lam p. lam seq.
    if null seq then []
    else if p (head seq) then cons (head seq) (filter p (tail seq))
    else (filter p (tail seq))
end

recursive
  let find = lam p. lam seq.
    if null seq then None ()
    else if p (head seq) then Some (head seq)
    else find p (tail seq)
end

let partition = (lam p. lam seq.
    (filter p seq, filter (lam q. if p q then false else true) seq))

let findAssoc = lam p. lam seq.
  match find (lam tup. p tup.0) seq with Some res
  then Some res.1
  else None ()

-- Removes duplicates with preserved ordering. Keeps first occurrence of an element.
let distinct = lam eq. lam seq.
  recursive let work = lam seq1. lam seq2.
    match seq1 with [h] ++ t
      then match find (eq h) seq2 with Some _
           then work t seq2
           else cons h (work t (cons h seq2))
    else []
  in work seq []

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

let max = lam cmp. min (lam l. lam r. cmp r l)

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

mexpr

utest head [2,3,5] with 2 in
utest tail [2,4,8] with [4,8] in

utest init [2,3,5] with [2,3] in
utest last [2,4,8] with 8 in

utest slice [1,3,5] 0 2 with [1,3] in
utest slice [3,7,10,20] 1 3 with [7,10,20] in
utest slice ['a','b'] 1 10 with ['b'] in
utest slice [1,3] 2 10 with [] in

utest mapi (lam i. lam x. i) [3,4,8,9,20] with [0,1,2,3,4] in
utest mapi (lam i. lam x. i) [] with [] in

utest map (lam x. addi x 1) [3,4,8,9,20] with [4,5,9,10,21] in
utest map (lam x. addi x 1) [] with [] in

utest foldl addi 0 [1,2,3,4,5] with 15 in
utest foldl addi 0 [] with 0 in
utest map (foldl addi 0) [[1,2,3], [], [1,3,5,7]] with [6, 0, 16] in

utest zipWith addi [1,2,3,4,5] [5, 4, 3, 2, 1] with [6,6,6,6,6] in
utest zipWith (zipWith addi) [[1,2], [], [10, 10, 10]] [[3,4,5], [1,2], [2, 3]]
      with [[4,6], [], [12, 13]] in
utest zipWith addi [] [] with [] in

utest foldr (lam x. lam acc. x) 0 [1,2] with 1 in
utest foldr (lam acc. lam x. x) 0 [] with 0 in
utest foldr cons [] [1,2,3] with [1,2,3] in
utest foldr1 (lam x. lam acc. (x,acc)) [1,2] with (1,2) in

utest join [[1,2],[3,4],[5,6]] with [1,2,3,4,5,6] in
utest join [[1,2],[],[5,6]] with [1,2,5,6] in
utest join [[],[],[]] with [] in

utest any (lam x. eqi x 1) [0, 4, 1, 2] with true in
utest any (lam x. eqi x 5) [0, 4, 1, 2] with false in
utest any (lam x. true) [] with false in
utest all (lam x. eqi x 1) [1, 1, 1, 2] with false in
utest all (lam x. eqi x 0) [0, 0, 0] with true in
utest all (lam x. eqi x 1) [] with true in

utest filter (lam x. eqi x 1) [1,2,4] with [1] in
utest filter (lam _. false) [3,5,234,1,43] with [] in
utest filter (lam x. gti x 2) [3,5,234,1,43] with [3,5,234,43] in

utest find (lam x. eqi x 2) [4,1,2] with Some 2 in
utest find (lam x. lti x 1) [4,1,2] with None () in

utest findAssoc (eqi 1) [(2,3), (1,4)] with Some 4 in
utest findAssoc (eqi 3) [(2,3), (1,4)] with None () in

utest partition (lam x. gti x 3) [4,5,78,1] with ([4,5,78],[1]) in
utest partition (lam x. gti x 0) [4,5,78,1] with ([4,5,78,1],[]) in

utest distinct eqi [] with [] in
utest distinct eqi [42,42] with [42] in
utest distinct eqi [1,1,2] with [1,2] in
utest distinct eqi [1,1,5,1,2,3,4,5,0] with [1,5,2,3,4,0] in

utest sort (lam l. lam r. subi l r) [3,4,8,9,20] with [3,4,8,9,20] in
utest sort (lam l. lam r. subi l r) [9,8,4,20,3] with [3,4,8,9,20] in
utest sort (lam l. lam r. subi r l) [9,8,4,20,3] with [20,9,8,4,3] in
utest sort (lam l. lam r. 0) [9,8,4,20,3] with [9,8,4,20,3] in
utest sort (lam l. lam r. subi l r) [] with [] in

utest min (lam l. lam r. subi l r) [3,4,8,9,20] with Some 3 in
utest min (lam l. lam r. subi l r) [9,8,4,20,3] with Some 3 in
utest min (lam l. lam r. subi l r) [] with None () in
utest max (lam l. lam r. subi l r) [3,4,8,9,20] with Some 20 in
utest max (lam l. lam r. subi l r) [9,8,4,20,3] with Some 20 in

utest unfoldr (lam b. if eqi b 10 then None () else Some (b, addi b 1)) 0
with [0,1,2,3,4,5,6,7,8,9] in

utest index (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 1 in
utest index (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 4 in

utest lastIndex (lam x. eqi (length x) 2) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 3 in
utest lastIndex (lam x. null x) [[1,2,3], [1,2], [3], [1,2], [], [1]] with Some 4 in

()
