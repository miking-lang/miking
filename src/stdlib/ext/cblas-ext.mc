/-

  MCore High-level CBLAS interface

  The interface mostly mirrors:
    https://ocaml.xyz/owl/owl/Owl_cblas_basic/index.html.

  For CBLAS documentation see:
    https://software.intel.com/en-us/mkl-developer-reference-c

-/

include "option.mc"
include "int.mc"
include "arr-ext.mc"

-- Matrix array layout flag.
type CBLASLayout
external cblasRowMajor : CBLASLayout
external cblasColMajor : CBLASLayout
external cblasLayoutEq : CBLASLayout -> CBLASLayout -> Bool

utest cblasLayoutEq cblasRowMajor cblasRowMajor with true
utest cblasLayoutEq cblasColMajor cblasColMajor with true
utest cblasLayoutEq cblasRowMajor cblasColMajor with false
utest cblasLayoutEq cblasColMajor cblasRowMajor with false

-- Matrix transpose flag.
type CBLASTranspose
external cblasNoTrans : CBLASTranspose
external cblasTrans : CBLASTranspose
-- external cblasConjTrans : CBLASTranspose -- NOTE(oerikss, 2025-02-24): Enable this when/if we add a complex kind to external arrays.
external cblasTransEq : CBLASTranspose -> CBLASTranspose -> Bool

utest cblasTransEq cblasNoTrans cblasNoTrans with true
utest cblasTransEq cblasTrans cblasTrans with true
utest cblasTransEq cblasNoTrans cblasTrans with false
utest cblasTransEq cblasTrans cblasNoTrans with false

-- Triangular matrix flag.
type CBLASTriangular
external cblasUpperTriag : CBLASTriangular
external cblasLowerTriag : CBLASTriangular
external cblasTriagEq : CBLASTriangular -> CBLASTriangular -> Bool

utest cblasTriagEq cblasUpperTriag cblasUpperTriag with true
utest cblasTriagEq cblasLowerTriag cblasLowerTriag with true
utest cblasTriagEq cblasUpperTriag cblasLowerTriag with false
utest cblasTriagEq cblasLowerTriag cblasUpperTriag with false

-- Diagonal matrix flag.
type CBLASDiagonal
external cblasNonUnitDiag : CBLASDiagonal
external cblasUnitDiag : CBLASDiagonal
external cblasDiagEq : CBLASDiagonal -> CBLASDiagonal -> Bool

utest cblasDiagEq cblasNonUnitDiag cblasNonUnitDiag with true
utest cblasDiagEq cblasUnitDiag cblasUnitDiag with true
utest cblasDiagEq cblasNonUnitDiag cblasUnitDiag with false
utest cblasDiagEq cblasUnitDiag cblasNonUnitDiag with false

-- Matrix side flag.
type CBLASSide
external cblasLeftSide : CBLASSide
external cblasRightSide : CBLASSide
external cblasSideEq : CBLASSide -> CBLASSide -> Bool

utest cblasSideEq cblasLeftSide cblasLeftSide with true
utest cblasSideEq cblasRightSide cblasRightSide with true
utest cblasSideEq cblasLeftSide cblasRightSide with false
utest cblasSideEq cblasRightSide cblasLeftSide with false

--------------------------------------------------------------------------------
-- Level-1 BLAS: vector-vector operations
--------------------------------------------------------------------------------

external externalCblasAxpy
  : all a. Int -> a -> ExtArr a -> Int -> ExtArr a -> Int -> ()

type CBLASAxpyArg = {n : Option Int, incx : Int, incy : Int}

let cblasAxpyArg : CBLASAxpyArg = {
  n = None (),
  incx = 1,
  incy = 1
}

-- .brief Computes y := a*x + y.
--
-- .see https://www.intel.com/content/www/us/en/docs/onemkl/developer-reference-c/2024-0/cblas-axpy.html
--
-- .lam[arg.n]    Number of elements in x and y (default:
--                `min(length(x), lenth(y))`).
--
-- .lam[arg.incx] Increment for the elements of x (default: 1).
-- .lam[arg.incy] Increment for the elements of y (default: 1).
-- .lam[a]        The scalar a.
-- .lam[x]        The vector x.
-- .lam[y]        The vector y that will also hold the result of the
--                computation.
--
let cblasAxpy : all a. CBLASAxpyArg -> a -> ExtArr a -> ExtArr a -> ()
  = lam arg. lam a. lam x. lam y.
    let n =
      optionGetOrElse (lam. mini (extArrLength x) (extArrLength y)) arg.n
    in
    externalCblasAxpy n a x arg.incx y arg.incy

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let x = extArrOfSeq [1., 2., 3.] in
    let y = extArrOfSeq [4., 5., 6.] in
    let a = 2. in
    cblasAxpy cblasAxpyArg a x y;
    utest extArrToSeq x with [1., 2., 3.] in
    utest extArrToSeq y with [6., 9., 12.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
() with ()


external externalCblasCopy
  : all a. Int -> ExtArr a -> Int -> ExtArr a -> Int -> ()

type CBLASCopyArg = {n : Option Int, incx : Int, incy : Int}

let cblasCopyArg : CBLASAxpyArg = {
  n = None (),
  incx = 1,
  incy = 1
}

-- .brief Copies x to y.
--
-- .see https://www.intel.com/content/www/us/en/docs/onemkl/developer-reference-c/2024-0/cblas-copy.html
--
-- .lam[arg.n]    Number of elements in x and y (default:
--                `min(length(x), lenth(y))`).
--
-- .lam[arg.incx] Increment for the elements of x (default: 1).
-- .lam[arg.incy] Increment for the elements of y (default: 1).
-- .lam[x]        The vector x.
-- .lam[y]        The vector y that will also hold the result of the
--                computation.
--
let cblasCopy : all a. CBLASCopyArg -> ExtArr a -> ExtArr a -> ()
  = lam arg. lam x. lam y.
    let n =
      optionGetOrElse (lam. mini (extArrLength x) (extArrLength y)) arg.n
    in
    externalCblasCopy n x arg.incx y arg.incy

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let x = extArrOfSeq [1., 2., 3.] in
    let y = extArrMakeUninit kind 3 in
    cblasCopy cblasCopyArg x y;
    utest extArrToSeq x with [1., 2., 3.] in
    utest extArrToSeq y with [1., 2., 3.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
() with ()


external externalCblasScal
  : all a. Int -> a -> ExtArr a -> Int -> ()

type CBLASScalArg = {n : Option Int, incx : Int}

let cblasScalArg : CBLASScalArg = {
  n = None (),
  incx = 1
}

-- .brief Computes x := a*x.
--
-- .see https://www.intel.com/content/www/us/en/docs/onemkl/developer-reference-c/2024-0/cblas-scal.html
--
-- .lam[arg.n]    Number of elements in x (default: `length(x)`)
-- .lam[arg.incx] Increment for the elements of x (default: 1).
-- .lam[a]        The scalar a.
-- .lam[x]        The vector x that will also hold the result of the
--                computation.
--
let cblasScal : all a. CBLASScalArg -> a -> ExtArr a -> ()
  = lam arg. lam a. lam x.
    let n = optionGetOrElse (lam. extArrLength x) arg.n in
    externalCblasScal n a x arg.incx

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let x = extArrOfSeq [1., 2., 3.] in
    cblasScal cblasScalArg 2. x;
    utest extArrToSeq x with [2., 4., 6.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
() with ()

--------------------------------------------------------------------------------
-- Level-2 BLAS: matrix-vector operations
--------------------------------------------------------------------------------

external externalCblasGemv
  : all a.
    CBLASLayout -> CBLASTranspose ->
    Int -> Int ->
    a ->
    ExtArr a -> Int ->
    ExtArr a -> Int ->
    a ->
    ExtArr a -> Int ->
    ()

type CBLASGemvArg a = {
  layout : CBLASLayout,
  transpose : Bool,
  incx : Int,
  incy : Int,
  alpha : a,
  beta : a
}

let cblasGemvArg : CBLASGemvArg Float = {
  layout = cblasRowMajor,
  transpose = false,
  incx = 1,
  incy = 1,
  alpha = 1.0,
  beta = 0.0
}

-- .brief Computes y := alpha*A*x + beta*y. By default y := A*x.
--
-- .see https://www.intel.com/content/www/us/en/docs/onemkl/developer-reference-c/2024-0/cblas-gemv.html
--
-- .lam[arg.layout]    Specifies 2D array storage layout
--                     (default: `cblasRowMajor`).
--
-- .lam[arg.transpose] Specifies the operation as:
--                     - false: y := alpha*A*x + beta*y.
--                     - true:  y := alpha*A*x + beta*y.
--                     (default: false).
--
-- .lam[arg.incx]   Increment for the elements of x (default: 1).
-- .lam[arg.incy]   Increment for the elements of y (default: 1).
--
-- .lam[arg.alpha]  The scalar alpha (default: 1.0)
-- .lam[arg.beta]   The scalar beta (default: 0.0)
-- .lam[m]          The number of rows in A.
-- .lam[n]          The number of columns in A.
-- .lam[a]          The m-by-n matrix A.
-- .lam[x]          The vector x.
-- .lam[y]          The vector y that will also hold the result of the
--                  computation.
--
let cblasGemv
  : all a. CBLASGemvArg a -> Int -> Int -> ExtArr a -> ExtArr a -> ExtArr a -> ()
  = lam arg. lam m. lam n. lam a. lam x. lam y.
    let transpose = if arg.transpose then cblasTrans else cblasNoTrans in
    let lda = if cblasLayoutEq arg.layout cblasRowMajor then n else m in
    externalCblasGemv
      arg.layout transpose m n arg.alpha a lda x arg.incx arg.beta y arg.incy

utest
  let test = lam kind.
    let extArrOfSeq = extArrOfSeq kind in
    let m = 2 in
    let n = 3 in
    let a = extArrOfSeq [1., 2., 3., 4., 5., 6.] in
    let x = extArrOfSeq [1., 2., 3.] in
    let y = extArrOfSeq [4., 5.] in
    let beta = 2. in
    cblasGemv { cblasGemvArg with beta = beta } m n a x y;
    utest extArrToSeq x with [1., 2., 3.] in
    utest extArrToSeq y with [22., 42.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
() with ()

--------------------------------------------------------------------------------
-- Level-3 BLAS: matrix-matrix operations
--------------------------------------------------------------------------------

external externalCblasGemm
  : all a.
    CBLASLayout -> CBLASTranspose -> CBLASTranspose ->
    Int -> Int -> Int ->
    a ->
    ExtArr a -> Int ->
    ExtArr a -> Int ->
    a ->
    ExtArr a -> Int ->
    ()

type CBLASGemmArg a = {
  layout : CBLASLayout,
  transposeA : Bool,
  transposeB : Bool,
  alpha : a,
  beta : a
}

let cblasGemmArg : CBLASGemmArg Float = {
  layout = cblasRowMajor,
  transposeA = false,
  transposeB = false,
  alpha = 1.0,
  beta = 0.0
}

-- .brief Computes C := alpha*op(A)*op(B) + beta*C. By default: C := A*B.
--
-- .see https://www.intel.com/content/www/us/en/docs/onemkl/developer-reference-c/2024-0/cblas-gemv.html
--
-- .lam[arg.layout]     Specifies 2D array storage layout
--                      (default: `cblasRowMajor`).
--
-- .lam[arg.transposeA] Specifies the operation as:
--                      - false: op(A) = A
--                      - true:  op(A) = A^T
--                      (default: false).
--
-- .lam[arg.transposeB] Specifies the operation as:
--                      - false: op(B) = B
--                      - true:  op(B) = B^T
--                      (default: false).
--
-- .lam[arg.alpha]  The scalar alpha (default: 1.0)
-- .lam[arg.beta]   The scalar beta (default: 0.0)
-- .lam[m]          The number of rows in A.
-- .lam[n]          The number of columns in B.
-- .lam[k]          The number of columns in A and the number of rows in B.
-- .lam[a]          The m-by-k matrix A.
-- .lam[b]          The k-by-n matrix B.
-- .lam[c]          The m-by-n matrix C that will also hold the result of
--                  the computation.
--
let cblasGemm
  : all a. CBLASGemmArg a -> Int -> Int -> Int -> ExtArr a -> ExtArr a -> ExtArr a -> ()
  = lam arg. lam m. lam n. lam k. lam a. lam b. lam c.
    let transposeA = if arg.transposeA then cblasTrans else cblasNoTrans in
    let transposeB = if arg.transposeB then cblasTrans else cblasNoTrans in
    let lda =
      if cblasLayoutEq arg.layout cblasRowMajor then
        if arg.transposeA then m else k
      else
        if arg.transposeA then k else m
    in
    let ldb =
      if cblasLayoutEq arg.layout cblasRowMajor then
        if arg.transposeB then k else n
      else
        if arg.transposeB then n else k
    in
    let ldc = if cblasLayoutEq arg.layout cblasRowMajor then n else m in
    externalCblasGemm
      arg.layout transposeA transposeB
      m n k
      arg.alpha
      a lda
      b ldb
      arg.beta
      c ldc

utest
  let test = lam kind.
    let as = [1., 2., 3., 4.] in
    let bs = [5., 6., 7., 8.] in

    let extArrOfSeq = extArrOfSeq kind in
    let n = 2 in
    let a = extArrOfSeq as in
    let b = extArrOfSeq bs in
    let c = extArrMakeUninit kind (muli n n)  in
    cblasGemm cblasGemmArg
      n n n a b c;
    utest extArrToSeq a with as in
    utest extArrToSeq b with bs in
    utest extArrToSeq c with [19., 22., 43., 50.] in
    cblasGemm { cblasGemmArg with transposeA = true }
      n n n a b c;
    utest extArrToSeq c with [26., 30., 38., 44.] in
    cblasGemm { cblasGemmArg with transposeB = true }
      n n n a b c;
    utest extArrToSeq c with [17., 23., 39., 53.] in
    cblasGemm { cblasGemmArg with transposeA = true, transposeB = true }
      n n n a b c;
    utest extArrToSeq c with [23., 31., 34., 46.] in
    cblasGemm { cblasGemmArg with layout = cblasColMajor }
      n n n a b c;

    let m = 3 in
    let n = 1 in
    let k = 2 in
    let a = extArrOfSeq [1., 2., 3., 4., 5., 6.] in
    let b = extArrOfSeq [7., 8.] in
    let c = extArrMakeUninit kind (muli m n) in
    cblasGemm cblasGemmArg
      m n k a b c;
    utest extArrToSeq c with [23.,53.,83.] in
    cblasGemm { cblasGemmArg with transposeA = true }
      m n k a b c;
    utest extArrToSeq c with [39.,54.,69.] in
    cblasGemm { cblasGemmArg with transposeB = true }
      m n k a b c;
    utest extArrToSeq c with [23.,53.,83.] in
    cblasGemm { cblasGemmArg with transposeA = true, transposeB = true }
      m n k a b c;
    utest extArrToSeq c with [39.,54.,69.] in
    cblasGemm { cblasGemmArg with layout = cblasColMajor }
      m n k a b c;

    let n = 2 in
    let a = extArrOfSeq [1., 3., 2., 4.] in
    let b = extArrOfSeq [5., 7., 6., 8.] in
    let c = extArrMakeUninit kind (muli n n)  in
    cblasGemm { cblasGemmArg with layout = cblasColMajor }
      n n n a b c;
    utest extArrToSeq c with [19., 43., 22., 50.] in
    cblasGemm { cblasGemmArg with layout = cblasColMajor, transposeA = true }
      n n n a b c;
    utest extArrToSeq c with [26., 38., 30., 44.] in
    cblasGemm { cblasGemmArg with layout = cblasColMajor, transposeB = true }
      n n n a b c;
    utest extArrToSeq c with [17., 39., 23., 53.] in
    cblasGemm { cblasGemmArg with
                layout = cblasColMajor, transposeA = true, transposeB = true }
      n n n a b c;
    utest extArrToSeq c with [23., 34., 31., 46.] in
    ()
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
() with ()
