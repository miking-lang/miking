/-

  High-level matrix library.

-/

include "either.mc"
include "arr-ext.mc"
include "cblas-ext.mc"

-- Enumerates matrix operation errors.
type MatError
con DimensionMismatch : () -> MatError
con NotSquare : () -> MatError

-- String representation of a matrix error.
let matErrorToString : MatError -> String
  = lam err.
    switch err
    case DimensionMismatch _ then "Dimension mismatch"
    case NotSquare _ then "Not square"
    end

--------------------------------------------------------------------------------
-- External array based matrix with row-major layout
--------------------------------------------------------------------------------

-- External Matrix.
type Mat a = {
  m : Int,
  n : Int,
  arr : ExtArr a
}

-- Creates an unitialized matrix.
let matMakeUninit
  : all a. ExtArrKind a -> Int -> Int -> Mat a
  = lam kind. lam m. lam n. {
    m = m,
    n = n,
    arr = externalExtArrMakeUninit kind (muli m n)
  }

-- Creates a matrix.
let matMake
  : all a. ExtArrKind a -> Int -> Int -> a -> Mat a
  = lam kind. lam m. lam n. lam v. {
    m = m,
    n = n,
    arr = extArrMake kind (muli m n) v
  }

-- Gets the `ij`th element from the matrix.
let matGetExn : all a. Mat a -> Int -> Int -> a
  = lam a. lam i. lam j. externalExtArrGet a.arr (addi (muli i a.n) j)

-- Sets the `ij`th element of the matrix to the value `v` inplace.
let matSetExn : all a. Mat a -> Int -> Int -> a -> ()
  = lam a. lam i. lam j. lam v.
    externalExtArrSet a.arr (addi (muli i a.n) j) v

utest
  let test = lam kind.
    let a  = matMakeUninit kind 2 3 in
    utest matSetExn a 0 0 0. with () in
    utest matSetExn a 0 1 1. with () in
    utest matSetExn a 0 2 2. with () in
    utest matSetExn a 1 0 3. with () in
    utest matSetExn a 1 1 4. with () in
    utest matSetExn a 1 2 5. with () in
    utest matGetExn a 0 0 with 0. in
    utest matGetExn a 0 1 with 1. in
    utest matGetExn a 0 2 with 2. in
    utest matGetExn a 1 0 with 3. in
    utest matGetExn a 1 1 with 4. in
    utest matGetExn a 1 2 with 5. in
    utest extArrGetExn a.arr 0 with 0. in
    utest extArrGetExn a.arr 1 with 1. in
    utest extArrGetExn a.arr 2 with 2. in
    utest extArrGetExn a.arr 3 with 3. in
    utest extArrGetExn a.arr 4 with 4. in
    utest extArrGetExn a.arr 5 with 5. in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  ()
  with ()


-- Creates a matrix from an external array where the matrix and array shares
-- data.
let matFromArrExn : all a. Int -> Int -> ExtArr a -> Mat a
  = lam m. lam n. lam a.
    if eqi (muli m n) (extArrLength a) then { m = m, n = n, arr = a }
    else error "matFromArrExn: dimensions mismatch"

utest
  extArrToSeq
    (matFromArrExn 1 3 (extArrOfSeq extArrKindFloat64 [1., 2., 3.])).arr
  with [1., 2., 3.]


-- Copies an matrix.
let matCopy : all a. Mat a -> Mat a
  = lam a.
    let mn = muli a.m a.n in
    let b = extArrMakeUninit (externalExtArrKind a.arr) mn in
    externalCblasCopy mn a.arr 1 b 1;
    { a with arr = b }

utest
  let a =
    matCopy (matFromArrExn 1 3 (extArrOfSeq extArrKindFloat64 [1., 2., 3.]))
  in
  utest a.m with 1 in
  utest a.n with 3 in
  utest extArrToSeq a.arr with [1., 2., 3.] in
  () with ()

--------------------------------------------------------------------------------
-- Inplace matrix operations. These operations do not allocate new data.
--------------------------------------------------------------------------------

-- Two matrices has the same shape.
let matHasSameShape2 = lam a. lam b. and (eqi a.m b.m) (eqi a.n b.n)

-- Three matrices has the same shape.
let matHasSameShape3 = lam a. lam b. lam c.
  and (matHasSameShape2 a b) (matHasSameShape2 b c)

-- Matrix is square.
let matIsSquare = lam a. eqi a.m a.n

external externalMatTranspose : Int -> Int -> ExtArr Float -> ExtArr Float -> ()

-- General matrix transpose. assumes that both operands has the same layout.
let matTranposeNoAlloc : Mat Float -> Mat Float ->  Either MatError ()
  = lam a. lam b.
    if and (eqi a.m b.n) (eqi a.n b.m) then
      externalMatTranspose a.m a.n a.arr b.arr;
      Right ()
    else Left (DimensionMismatch ())

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matMakeUninit kind 2 3 in
    utest matTranposeNoAlloc a b with Right () in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with [1., 3., 5., 2., 4., 6.] in
    let b = matMakeUninit kind 3 2 in
    utest extArrToSeq a.arr with as in
    utest matTranposeNoAlloc a b with Left (DimensionMismatch ()) in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


external externalMatElemMul
  : Int -> Int -> ExtArr Float -> ExtArr Float -> ExtArr Float -> ()

-- General matrix element-wise addition.
let matElemMulNoAlloc
  : Mat Float -> Mat Float -> Mat Float ->  Either MatError ()
  = lam a. lam b. lam c.
    if matHasSameShape3 a b c then
      externalMatElemMul a.m a.n a.arr b.arr c.arr;
      Right ()
    else Left (DimensionMismatch ())

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let bs = [7., 8., 9., 10., 11., 12.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matFromArrExn 3 2 (extArrOfSeq bs) in
    let c = matMakeUninit kind 3 2 in
    utest matElemMulNoAlloc a b c with Right () in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with bs in
    utest extArrToSeq c.arr with [7.,16.,27.,40.,55.,72.] in
    let a = matMakeUninit kind 3 2 in
    let b = matMakeUninit kind 3 3 in
    let c = matMakeUninit kind 3 3 in
    utest matElemMulNoAlloc a b c with Left (DimensionMismatch ()) in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


external externalMatElemExp
  : Int -> Int -> ExtArr Float -> ExtArr Float -> ()

-- General matrix element-wise exp.
let matElemExpInplace
  : Mat Float -> Mat Float -> Either MatError ()
  = lam a. lam b.
    if matHasSameShape2 a b then
      externalMatElemExp a.m a.n a.arr b.arr;
      Right ()
    else Left (DimensionMismatch ())

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matMakeUninit kind 3 2 in
    utest matElemExpInplace a b with Right () in
    utest extArrToSeq a.arr with as in
    utest map floorfi (extArrToSeq b.arr) with [2, 7, 20, 54, 148, 403] in
    let a = matMakeUninit kind 3 2 in
    let b = matMakeUninit kind 3 3 in
    utest matElemExpInplace a b with Left (DimensionMismatch ()) in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


external externalMatElemLog
  : Int -> Int -> ExtArr Float -> ExtArr Float -> ()

-- General matrix element-wise log.
let matElemLogInplace
  : Mat Float -> Mat Float -> Either MatError ()
  = lam a. lam b.
    if matHasSameShape2 a b then
      externalMatElemLog a.m a.n a.arr b.arr;
      Right ()
    else Left (DimensionMismatch ())

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [2., 7., 20., 54., 148., 403.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matMakeUninit kind 3 2 in
    utest matElemLogInplace a b with Right () in
    utest extArrToSeq a.arr with as in
    utest map floorfi (extArrToSeq b.arr) with [0, 1, 2, 3, 4, 5] in
    let a = matMakeUninit kind 3 2 in
    let b = matMakeUninit kind 3 3 in
    utest matElemLogInplace a b with Left (DimensionMismatch ()) in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()

--------------------------------------------------------------------------------
-- Referentially transparent matrix operations.
--------------------------------------------------------------------------------

-- Returns the transpose of a matrix as a fresh matrix.
let matTranspose : Mat Float -> Mat Float
  = lam a.
    let b = matMakeUninit (externalExtArrKind a.arr) a.n a.m in
    matTranposeNoAlloc a b;
    b

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matTranspose a in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with [1., 3., 5., 2., 4., 6.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix element-wise multiplication. Returns a fresh matrix.
let matElemMul : Mat Float -> Mat Float -> Either MatError (Mat Float)
  = lam a. lam b.
    if matHasSameShape2 a b then
      let c = matMakeUninit (externalExtArrKind a.arr) a.m a.n in
      matElemMulNoAlloc a b c;
      Right c
    else Left (DimensionMismatch ())

let matElemMulExn : Mat Float -> Mat Float -> Mat Float
  = lam a. lam b.
    eitherEither
      (lam err. error (matErrorToString err)) (lam x. x) (matElemMul a b)

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let bs = [7., 8., 9., 10., 11., 12.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matFromArrExn 3 2 (extArrOfSeq bs) in
    let c = matElemMulExn a b in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with bs in
    utest extArrToSeq c.arr with [7.,16.,27.,40.,55.,72.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix element-wise exp. Returns a fresh matrix.
let matElemExp : Mat Float -> Mat Float
  = lam a.
    let b = matMakeUninit (externalExtArrKind a.arr) a.m a.n in
    matElemExpInplace a b;
    b

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matElemExp a in
    utest extArrToSeq a.arr with as in
    utest map floorfi (extArrToSeq b.arr) with [2, 7, 20, 54, 148, 403] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix element-wise log. Returns a fresh matrix.
let matElemLog : Mat Float -> Mat Float
  = lam a.
    let b = matMakeUninit (externalExtArrKind a.arr) a.m a.n in
    matElemLogInplace a b;
    b

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [2., 7., 20., 54., 148., 403.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matElemLog a in
    utest extArrToSeq a.arr with as in
    utest map floorfi (extArrToSeq b.arr) with [0, 1, 2, 3, 4, 5] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix addition. Returns a fresh matrix.
let matAdd : Mat Float -> Mat Float -> Either MatError (Mat Float)
  = lam a. lam b.
    if matHasSameShape2 a b then
      let m = a.m in
      let n = a.n in
      let c = matMakeUninit (externalExtArrKind b.arr) m n in
      let mn = muli m n in
      externalCblasCopy mn b.arr 1 c.arr 1;
      externalCblasAxpy mn 1. a.arr 1 c.arr 1;
      Right c
    else Left (DimensionMismatch ())

let matAddExn : Mat Float -> Mat Float -> Mat Float
  = lam a. lam b.
    eitherEither
      (lam err. error (matErrorToString err)) (lam x. x) (matAdd a b)

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let bs = [7., 8., 9., 10., 11., 12.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matFromArrExn 3 2 (extArrOfSeq bs) in
    let c = matAddExn a b in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with bs in
    utest extArrToSeq c.arr with [8., 10., 12., 14., 16., 18.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix scalar multiplicaiton. Returns a fresh matrix.
let matScale : Float -> Mat Float -> Mat Float
  = lam s. lam a.
    let m = a.m in
    let n = a.n in
    let b = matMakeUninit (externalExtArrKind a.arr) m n in
    let mn = muli m n in
    externalCblasCopy mn a.arr 1 b.arr 1;
    externalCblasScal mn s b.arr 1;
    b

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matScale 2. a in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with [2., 4., 6., 8., 10., 12.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- General matrix multiplication. Returns a fresh matrix.
let matMul : Mat Float -> Mat Float -> Either MatError (Mat Float)
  = lam a. lam b.
    let m = a.m in
    let n = b.n in
    let k = a.n in
    if eqi k b.m then
      let c = matMakeUninit (externalExtArrKind b.arr) m n in
      externalCblasGemm
        cblasRowMajor cblasNoTrans cblasNoTrans
        m n k
        1.
        a.arr k
        b.arr n
        0.
        c.arr n;
      Right c
    else Left (DimensionMismatch ())

let matMulExn : Mat Float -> Mat Float -> Mat Float
  = lam a. lam b.
    eitherEither
      (lam err. error (matErrorToString err)) (lam x. x) (matMul a b)

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let as = [1., 2., 3., 4., 5., 6.] in
    let bs = [7., 8., 9., 10., 11., 12.] in
    let a = matFromArrExn 3 2 (extArrOfSeq as) in
    let b = matFromArrExn 2 3 (extArrOfSeq bs) in
    let c = matMulExn a b in
    utest extArrToSeq a.arr with as in
    utest extArrToSeq b.arr with bs in
    utest extArrToSeq c.arr with
      [27., 30., 33., 61., 68., 75., 95., 106., 117.]
    in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


external externalMatExp : Int -> Int -> ExtArr Float -> ExtArr Float

-- Computes the matrix exponential. Returns a fresh matrix.
-- .see https://ocaml.xyz/owl/owl/Owl_linalg/Generic/index.html#val-expm
let matExp : Mat Float -> Either MatError (Mat Float) =
  lam a.
    if matIsSquare a then Right { a with arr = externalMatExp a.m a.n a.arr }
    else Left (NotSquare ())

let matExpExn : Mat Float -> Mat Float
  = lam a.
    eitherEither
      (lam err. error (matErrorToString err)) (lam x. x) (matExp a)

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    utest matExp (matMakeUninit kind 2 3) with Left (NotSquare ()) in
    let as = [1., 2., 3., 4.] in
    let a = matFromArrExn 2 2 (extArrOfSeq as) in
    let b = matExpExn a in
    utest extArrToSeq a.arr with as in
    utest map floorfi (extArrToSeq b.arr) with [51, 74, 112, 164] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()


-- TODO(oerikss, 2025-02-27): Add additional matrix operations. For each
-- operation first see if it is part BLAS. If so, implement that in clbas-ext.mc
-- and then implement it here using that.
