include "option.mc"

let head = lam s. nth s 0
let tail = lam s. slice s 1 (length s)
let null = lam seq. eqi 0 (length seq)

-- Maps and folds
let map = fix (lam map. lam f. lam seq.
  if null seq then []
  else cons (f (head seq)) (map f (tail seq))
)

let foldl = fix (lam foldl. lam f. lam acc. lam seq.
    if null seq then acc
    else foldl f (f acc (head seq)) (tail seq)
)
let foldl1 = lam f. lam l. foldl f (head l) (tail l)

let foldr = fix (lam foldr. lam f. lam acc. lam seq.
    if null seq
    then acc
    else f (head seq) (foldr f acc (tail seq))
)

let foldr1 = lam f. lam seq. foldl1 (lam acc. lam x. f x acc) (reverse seq)

let zipWith = fix (lam zipWith. lam f. lam seq1. lam seq2.
    if null seq1 then []
    else if null seq2 then []
    else cons (f (head seq1) (head seq2)) (zipWith f (tail seq1) (tail seq2))
)

-- Predicates
let any = fix (lam any. lam p. lam seq.
  if null seq
  then false
  else or (p (head seq)) (any p (tail seq)))

let all = fix (lam all. lam p. lam seq.
  if null seq
  then true
  else and (p (head seq)) (all p (tail seq)))

-- Join
let join = lam seqs. foldl concat [] seqs

-- Searching
let filter = fix (lam filter. lam p. lam seq.
  if null seq then []
  else if p (head seq) then cons (head seq) (filter p (tail seq))
  else (filter p (tail seq)))

let find = fix (lam find. lam p. lam seq.
  if null seq then None
  else if p (head seq) then Some (head seq)
  else find p (tail seq))

let partition = (lam p. lam seq.
    (filter p seq, filter (lam q. if p q then false else true) seq))

mexpr

utest head [2,3,5] with 2 in
utest tail [2,4,8] with [4,8] in

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
utest find (lam x. lti x 1) [4,1,2] with None in

utest partition (lam x. gti x 3) [4,5,78,1] with ([4,5,78],[1]) in

()
