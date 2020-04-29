-- A simple library that defines matrix operations over sequences of sequences.
-- Matrices are represented as sequences of rows, represented as sequences.

include "vec.mc"

-- True if mtx is a matrix, otherwise false.
let matrixIsMatrix = lam mtx.
  and (not (null mtx))
      (all (lam row. and (eqi (length (head mtx)) (length row))
                         (gti (length row) 0))
           mtx)

-- Makes matrix of dimensions d = (m, n) with elements c.
let matrixConst = lam d. lam c. makeSeq d.0 (makeSeq d.1 c)

-- Get element (i, j) from matrix mtx.
let matrixGet = lam mtx. lam i. lam j. get (get mtx i) j

-- Set element (i, j) of matrix mtx to v
let matrixSet = lam mtx. lam i. lam j. lam v. set mtx i (set (get mtx i) j v)

-- Apply binary operator bop elementwise over the matrices mtx1 and mtx2.
-- Results in an error if mtx1 and mtx2 are of different dimensions or empty.
let matrixBop = lam bop. lam mtx1. lam mtx2.
  if neqi (length mtx1) (length mtx2) then
    error dimensionsMismatchMsg
  else if eqi (length mtx1) 0 then
    error emptyMsg
  else
    zipWith (vecBop bop) mtx1 mtx2

-- Applies function f i j x, row-wise, over the elements of mtx, where i, j is
-- the index of element and x its value.
let matrixMapij = lam f. lam mtx.
  mapi (lam i. lam c. mapi (lam j. lam v. f i j v) c) mtx

-- Applies function f x over the elements of mtx, where x is the elements value.
let matrixMap = lam f. matrixMapij (lam _. lam _. lam x. f x)

-- Size of matrix mtx
let matrixSize = lam mtx. (length mtx, length (get mtx 0))

-- Transpose matrix mtx
let matrixTr = lam mtx.
  recursive let work = lam mtx.
    if null mtx then []
    else if null (head mtx) then []
    else cons (map head mtx) (work (map tail mtx))
  in work mtx

-- Performs matrix multiplication between mtx1 and mtx2 where addition is
-- defined by add and multiplication is defined by mul.
-- Results in an error if dimensions of mtx1 and mtx2 does not match.
let matrixMul = lam add. lam mul. lam mtx1. lam mtx2.
  let s1 = matrixSize mtx1 in
  let s2 = matrixSize mtx2 in
  if or (neqi s1.0 s2.1) then
    error dimensionsMismatchMsg
  else
    let m2tr = matrixTr mtx2 in
    map (lam row. map (lam col. vecDot add mul col row) m2tr) mtx1

mexpr

let matrixAdd = matrixBop addi in
let matrixSMul = lam s. matrixMap (muli s) in
let matrixMul = matrixMul addi muli in

utest matrixConst (2,3) 0 with [[0,0,0],[0,0,0]] in

let A = [[1,3],[2,4]] in

utest matrixIsMatrix A with true in
utest matrixIsMatrix [] with false in
utest matrixIsMatrix [[]] with false in
utest matrixIsMatrix [[1, 2], [1]] with false in

utest matrixGet A 0 0 with 1 in
utest matrixGet A 1 0 with 2 in
utest matrixGet A 0 1 with 3 in
utest matrixGet A 1 1 with 4 in

let C = matrixConst (2,2) 0 in
let B = matrixSet C 0 0 1 in
let B = matrixSet B 1 0 2 in
let B = matrixSet B 0 1 3 in
let B = matrixSet B 1 1 4 in

utest B with A in
utest matrixAdd A B with [[2,6],[4,8]] in

utest matrixMapij (lam i. lam j. lam _. (i, j)) (matrixConst (2,2) (0,0))
with [[(0,0),(0,1)],[(1,0),(1,1)]] in

utest matrixSMul 3 A with [[3,9],[6,12]] in

utest matrixSize A with (2,2) in

utest matrixTr (matrixTr A) with A in
utest matrixTr A with [[1,2], [3,4]] in
utest matrixTr [[1,2,3], [4,5,6]] with [[1,4], [2,5], [3,6]] in

utest matrixMul [[1]] [[1]] with [[1]] in
utest matrixMul [[1], [2]] [[1, 2]] with [[1,2], [2,4]] in
utest matrixMul [[1,2]] [[1],[2]] with [[5]] in
utest matrixMul [[1],[2]] [[3]] with [[3],[6]] in

()
