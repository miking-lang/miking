-- A simple library that defines vector operations over sequences.

include "seq.mc"

let dimensionsMismatchMsg = "Dimensions mismatch"
let emptyMsg = "Empty"

-- True if seq represents a vector.
let vecIsVec = lam seq. not (null seq)

-- Apply binary operator bop elementwise over the sequences seq1 and seq2.
-- Results in an error if seq1 and seq2 are of different dimensions or empty.
let vecBop = lam bop. lam seq1. lam seq2.
  if neqi (length seq1) (length seq2) then
    error dimensionsMismatchMsg
  else if null seq1 then
    error emptyMsg
  else
    zipWith bop seq1 seq2

-- Performs the dotproduct between seq1 and seq2 with addition defined by add
-- and multiplication defined by mul.
-- Results in an error if seq1 and seq2 are of different dimensions or empty.
let vecDot = lam add. lam mul. lam seq1. lam seq2. foldl1 add (vecBop mul seq1 seq2)

mexpr

let dot = vecDot addi muli in
let inv = map (subi 0) in
let add = vecBop addi in
let mul = lam s. map (muli s) in

utest vecIsVec [0, 0, 0] with true in
utest add [1, 2, 3] (inv [1, 2, 3]) with [0, 0, 0] in
utest add [1, 2, 3] [1, 2, 3] with [2, 4, 6] in
utest mul 3 [1, 2, 3] with [3, 6, 9] in
utest dot [1, 2, 3] [1, 2, 3] with 14 in

()
