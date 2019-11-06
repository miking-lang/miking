let head = lam s. nth s 0
let tail = lam s. slice s 1 (length s)
let null = lam seq. eqi 0 (length seq)

-- Maps and folds
let map = fix (lam map. lam f. lam seq.
  if eqi (length seq) 0 then []
  else cons (f (head seq)) (map f (tail seq))
)

let foldl = fix (lam foldl. lam f. lam acc. lam seq.
    if eqi (length seq) 0 then acc
    else foldl f (f acc (head seq)) (tail seq)
)
let foldl1 = lam f. lam l. foldl f (head l) (tail l)

let zipWith = fix (lam zipWith. lam f. lam seq1. lam seq2.
    if eqi (length seq1) 0 then []
    else if eqi (length seq2) 0 then []
    else cons (f (head seq1) (head seq2)) (zipWith f (tail seq1) (tail seq2))
)

-- Predicates
let any  = fix (lam any. lam p. lam seq.
  if eqi (length seq) 0
  then false
  else or (p (head seq)) (any p (tail seq)))

let all = fix (lam all. lam p. lam xs.
  if eqi (length xs) 0
  then true
  else and (p (nth xs 0)) (all p (slice xs 1 (length xs))))


main
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
()